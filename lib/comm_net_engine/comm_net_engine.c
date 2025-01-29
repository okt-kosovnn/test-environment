/* SPDX-License-Identifier: Apache-2.0 */
/** @file
 * @brief RCF Network Communication Library
 *
 * C interface for network communication library
 *
 * Copyright (C) 2004-2022 OKTET Labs Ltd. All rights reserved.
 */

#include "te_config.h"

#include <stdio.h>
#include <stdlib.h>
#include <ctype.h>

#if HAVE_STRING_H
#include <string.h>
#endif
#if HAVE_UNISTD_H
#include <unistd.h>
#endif
#if HAVE_SYS_TYPES_H
#include <sys/types.h>
#endif
#if HAVE_SYS_SOCKET_H
#include <sys/socket.h>
#endif
#if HAVE_SYS_ERRNO_H
#include <sys/errno.h>
#endif
#if HAVE_ARPA_INET_H
#include <arpa/inet.h>
#endif
#if HAVE_NETINET_IN_H
#include <netinet/in.h>
#endif
#if HAVE_NETINET_TCP_H
#include <netinet/tcp.h>
#endif
#if HAVE_NETDB_H
#include <netdb.h>
#endif

#include "te_alloc.h"
#include "te_errno.h"
#include "comm_net_engine.h"


#ifndef TE_COMM_DEBUG_PROTO
/** Use '\n' as separator? */
#define TE_COMM_DEBUG_PROTO
#endif


/** @name Engine Network Communication library retry parameters */

/** Maximum number of connect retries */
#define TE_COMM_NET_ENGINE_RETRY_MAX        10

/** Timeout in seconds between connect retries to Test Agent */
#define TE_COMM_NET_ENGINE_RETRY_TIMEOUT    1

/*@}*/


/**
 * This structure  stores the information about each connection
 * and pointer to instances of this structure is used as handler
 */
struct rcf_net_connection{
    int     socket;         /**< Connection socket */
    size_t  bytes_to_read;  /**< Number of bytes of attachment to read */
};


/* Static function declaration. See implementation for comments */
static int find_attach(char *buf, size_t len);
static int read_socket(int socket, char *buffer, size_t len);


/**
 * Connects to the Test Agent side of Network Communication library.
 *
 * @param  addr         network address of the test agent
 * @param  port         port of the test agent
 * @param  p_rnc        pointer to to pointer to the rcf_net_connection
 *                      structure to be filled, used as handler
 * @param  p_select_set pointer to the fdset for reading to be modified
 *
 * @return Status code.
 * @retval 0            Success.
 * @retval other value  errno.
 */
int
rcf_net_engine_connect(const char *addr, const char *port,
                       struct rcf_net_connection **p_rnc,
                       fd_set *p_select_set)
{
    int                 s;
    int                 rc;
    struct addrinfo     hints;
    struct addrinfo    *res;
    unsigned int        retry = 0;

    memset(&hints, 0, sizeof(hints));
    /* Service is always in numeric format */
    hints.ai_flags = AI_NUMERICSERV;
    /* Only IPv4 is supported for now */
    hints.ai_family = AF_INET;
    /* comm_net_* libraries use TCP */
    hints.ai_socktype = SOCK_STREAM;

    rc = getaddrinfo(addr, port, &hints, &res);
    switch (rc)
    {
        case 0:
            /* success */
            break;

        case EAI_NONAME:
            return TE_RC(TE_COMM, TE_EHOSTUNREACH);

        case EAI_ADDRFAMILY:
            return TE_RC(TE_COMM, TE_EAFNOSUPPORT);

        case EAI_NODATA:
            return TE_RC(TE_COMM, TE_ENODATA);

        case EAI_AGAIN:
            return TE_RC(TE_COMM, TE_EAGAIN);

        case EAI_SYSTEM:
            return TE_OS_RC(TE_COMM, errno);

        default:
            return TE_RC(TE_COMM, TE_EFAIL);
    }

    /* Use the first addrinfo entry only */
    s = socket(res->ai_family, res->ai_socktype, res->ai_protocol);
    if (s < 0)
    {
        rc = errno;
        freeaddrinfo(res);
        return TE_OS_RC(TE_COMM, rc);
    }

    do {

        rc = connect(s, res->ai_addr, res->ai_addrlen);

    } while ((rc != 0) &&
             ((++retry) < TE_COMM_NET_ENGINE_RETRY_MAX) &&
             (sleep(TE_COMM_NET_ENGINE_RETRY_TIMEOUT) == 0));

    if (rc != 0)
    {
        rc = errno;
        freeaddrinfo(res);
        fprintf(stderr, "%s(): %s %s:%s\n",
                __FUNCTION__, strerror(rc), addr, port);
        return TE_OS_RC(TE_COMM, rc);
    }

    freeaddrinfo(res);

#if defined(TCP_NODELAY) || defined(SO_KEEPALIVE)
    {
        int optval;

#ifdef TCP_NODELAY
        /* Set TCE_NODELAY=1 to force TCP to send all data ASAP. */
        optval = 1;
        if (setsockopt(s, SOL_TCP, TCP_NODELAY,
                       &optval, sizeof(optval)) != 0)
        {
            rc = errno;
            perror("setsockopt(SOL_TCP, TCP_NODELAY, enabled)");
            (void)close(s);
            return TE_OS_RC(TE_COMM, rc);
        }
#endif
#ifdef SO_KEEPALIVE
#ifdef TCP_KEEPIDLE
        optval = TE_COMM_NET_ENGINE_KEEPIDLE;
        if (setsockopt(s, SOL_TCP, TCP_KEEPIDLE,
                       &optval, sizeof(optval)) != 0)
        {
            rc = errno;
            perror("setsockopt(SOL_TCP, TCP_KEEPIDLE)");
            (void)close(s);
            return TE_OS_RC(TE_COMM, rc);
        }
#endif
#ifdef TCP_KEEPINTVL
        optval = TE_COMM_NET_ENGINE_KEEPINTVL;
        if (setsockopt(s, SOL_TCP, TCP_KEEPINTVL,
                       &optval, sizeof(optval)) != 0)
        {
            rc = errno;
            perror("setsockopt(SOL_TCP, TCP_KEEPINTVL)");
            (void)close(s);
            return TE_OS_RC(TE_COMM, rc);
        }
#endif
#ifdef TCP_KEEPCNT
        optval = TE_COMM_NET_ENGINE_KEEPCNT;
        if (setsockopt(s, SOL_TCP, TCP_KEEPCNT,
                       &optval, sizeof(optval)) != 0)
        {
            rc = errno;
            perror("setsockopt(SOL_TCP, TCP_KEEPCNT)");
            (void)close(s);
            return TE_OS_RC(TE_COMM, rc);
        }
#endif
        optval = 1;
        if (setsockopt(s, SOL_SOCKET, SO_KEEPALIVE,
                       &optval, sizeof(optval)) != 0)
        {
            rc = errno;
            perror("setsockopt(SOL_SOCKET, SO_KEEPALIVE)");
            (void)close(s);
            return TE_OS_RC(TE_COMM, rc);
        }
#endif /* SO_KEEPALIVE */
    }
#endif /* defined(TCP_NODELAY) || defined(SO_KEEPALIVE) */

    FD_SET(s, p_select_set);

    /* Connection established. Let's allocate memory for rnc and fill it*/
    *p_rnc = TE_ALLOC(sizeof(**p_rnc));

    /* All field is set to zero. Just set the socket */
    (*p_rnc)->socket = s;

    return 0;
}

/**
 * Transmits data to the Test Agent via Network Communication library.
 *
 * @param  rnc          Handler received from rcf_net_engine_connect.
 * @param  data         Data to be transmitted.
 * @param  length       Length of the data.
 *
 * @return Status code.
 * @retval 0            Success.
 * @retval other value  errno.
 */
int
rcf_net_engine_transmit(struct rcf_net_connection *rnc,
                        const char *data, size_t length)
{
#define MAX_TRIES       1000
    ssize_t len = 0;
    int     tries = MAX_TRIES;
    int     err = 0;

    if (rnc == NULL)
        return TE_RC(TE_COMM, TE_EINVAL);

    while (length > 0 && tries > 0)
    {
        if ((len = send(rnc->socket, data, length, MSG_DONTWAIT)) < 0)
        {
            int err = errno;

            if (err == EWOULDBLOCK || err == EAGAIN)
            {
                usleep(10000);
                tries--;
                continue;
            }
            else
                return TE_OS_RC(TE_COMM, err);
        }

        length -= len;
        data += len;
        tries = MAX_TRIES;
    }
    if (length > 0)
        return TE_OS_RC(TE_COMM, err);

    return 0;
#undef MAX_TRIES
}


/**
 * Check, if some data are pending on the test agent connection. This
 * routine never blocks.
 *
 * @param rnc   Handler received from rcf_net_engine_connect.
 *
 * @return Status code.
 * @retval @c true     Data are pending.
 * @retval @c false    No data are pending.
 */
bool
rcf_net_engine_is_ready(struct rcf_net_connection *rnc)
{
    fd_set          rfds;
    struct timeval  tv;

    if (rnc == NULL)
        return false;

    if (rnc->bytes_to_read > 0)
        return true;

    FD_ZERO(&rfds);
    FD_SET(rnc->socket, &rfds);
    tv.tv_sec = 0;
    tv.tv_usec = 0;

    select(rnc->socket + 1, &rfds, NULL, NULL, &tv);

    return FD_ISSET(rnc->socket, &rfds) ? true : false;
}

/**
 * Receive data from the Test Agent via Network Communication library.
 *
 * @param rnc           Handler received from rcf_net_engine_connect
 * @param buffer        Buffer for data
 * @param pbytes        Pointer to variable with:
 *                      on entry - size of the buffer;
 *                      on return:
 *                      number of bytes really written if 0 returned
 *                      (success);
 *                      unchanged if TE_ESMALLBUF returned;
 *                      number of bytes in the message (with attachment)
 *                      if TE_EPENDING returned. (Note: If the function
 *                      called a number of times to receive one big
 *                      message, a full number of bytes will be returned
 *                      on first call.
 *                      On the next calls number of bytes in the message
 *                      minus number of bytes previously read by this
 *                      function will be returned);
 *                      undefined if other errno returned.
 * @param pba           Address of the pointer that will hold on return
 *                      an address of the first byte of the attachment (or
 *                      NULL if no attachment attached to the command). If
 *                      this function called more than once (to receive big
 *                      attachment) this pointer will be not touched.
 *
 * @return Status code.
 * @retval 0            Success (message received and written to the
 *                      buffer).
 * @retval TE_ESMALLBUF Buffer is too small for the message. The part of
 *                      the message is written to the buffer. Other part(s)
 *                      of the message can be read by the next calls to the
 *                      rcf_net_engine_receive. The ETSMALLBUF will be
 *                      returned until last part of the message will be
 *                      read.
 * @retval TE_EPENDING  Attachment is too big to fit into the buffer.
 *                      Part of the message with attachment is written
 *                      to the buffer. Other part(s) can be read by the
 *                      next calls to the rcf_net_engine_receive.
 *                      The TE_EPENDING will be returned until last part
 *                      of the message will be read.
 * @retval other value  errno.
 */
int
rcf_net_engine_receive(struct rcf_net_connection *rnc, char *buffer,
                       size_t *pbytes, char **pba)
{
    int     ret;
    size_t  l = 0;

    if (rnc == NULL)
        return TE_RC(TE_COMM, TE_EINVAL);

    if (rnc->bytes_to_read > 0)
    {
        /* Some data from previous message should be returned */
        if (rnc->bytes_to_read <= *pbytes)
        {
            /* Enough space */
            *pbytes = rnc->bytes_to_read;
            rnc->bytes_to_read = 0;
            return read_socket(rnc->socket, buffer, *pbytes);
        }
        else
        {
            /* Buffer is too small for the attachment */
            if ((ret = read_socket(rnc->socket, buffer, *pbytes)) != 0)
                return ret; /* Some error occurred */

            {
                int tmp = *pbytes;

                *pbytes = rnc->bytes_to_read;
                rnc->bytes_to_read -= tmp;
            }
            return TE_RC(TE_COMM, TE_EPENDING);
        }
    }

    while (1)
    {
        int r = recv(rnc->socket, buffer + l, 1, 0);

        if (r <= 0)
        {
            return TE_OS_RC(TE_COMM, r == 0 ? EPIPE : errno);
        }

        if (buffer[l] == 0
#ifdef TE_COMM_DEBUG_PROTO
            || buffer[l] == '\n'
#endif
            )
        {
            /* The whole message received */
            int attach_size;

#ifdef TE_COMM_DEBUG_PROTO
            if (buffer[l] == '\n')
            {
                buffer[l] = 0;           /* Change '\n' to zero... */

                if ((l > 0) && (buffer[l - 1] == '\r'))
                {
                    /* ... and change '\r' to the space */
                    buffer[l - 1] = ' ';
                }
            }
#endif

            l++;

            attach_size = find_attach(buffer, l);

            if (attach_size == -1)
            {
                /* No attachment */
                *pbytes = l;

                /* Set pba to NULL because no attachment attached */
                if (pba != NULL)
                    *pba = NULL;

                return 0;
            }
            else
            {
                /* Attachment found. */

                /* Set pba to the first byte of the attachment */
                if (pba != NULL)
                    *pba = buffer + l;

                if (*pbytes >= l + attach_size)
                {
                    /* Buffer is enough to write attachment */
                    *pbytes = l + attach_size;
                    return read_socket(rnc->socket, buffer + l,
                                       attach_size);
                }
                else
                {
                    /* Buffer is too small to write attachment */
                    int to_read = *pbytes - l;

                    ret = read_socket(rnc->socket, buffer + l, to_read);
                    if (ret != 0)
                    {
                        return ret; /* Some error occurred */
                    }

                    rnc->bytes_to_read = attach_size - to_read;
                    *pbytes = attach_size + l;
                    return TE_RC(TE_COMM, TE_EPENDING);
                }
            }
        }

        if (l == (*pbytes - 1))
            return TE_RC(TE_COMM, TE_ESMALLBUF);

        l += r;
    }
}


/**
 * Close connection (socket) to the Test Agent and release the memory used
 * by struct rcf_net_connection *rnc.
 *
 * @param p_rnc         Pointer to variable with  handler received from
 *                      rcf_net_engine_connect
 * @param p_select_set  Pointer to the fdset for reading to be modified
 *
 * @return Status code.
 * @retval 0            Success.
 * @retval other value  errno.
 */
int
rcf_net_engine_close(struct rcf_net_connection **p_rnc,
                     fd_set *p_select_set)
{
    int rc = 0;

    if (p_rnc == NULL)
        return TE_RC(TE_COMM, TE_EINVAL);

    if (*p_rnc == NULL)
        return 0;

    FD_CLR((*p_rnc)->socket, p_select_set);

    if (close((*p_rnc)->socket) < 0)
    {
        perror("rcf_net_engine_close(): close() error");
        rc = TE_OS_RC(TE_COMM, errno);
    }

    free(*p_rnc);
    *p_rnc = NULL;

    return rc;
}


/**
 * Search in the string for the "attach <number>" entry at the end. Inserts
 * ZERO before 'attach' word.
 *
 * @param str           String to process.
 * @param len           Length of the string.
 *
 * @return Status code.
 * @retval -1           No such entry found.
 * @retval other value  Number (value) from the entry.
 */
static int
find_attach(char *buf, size_t len)
{
    /* Pointer tmp will scan the buffer */
    char       *tmp;
    /* Pointer number will hold the address of the "<number>" entry */
    const char *number;


    /* Strings less than 9 chars can not contain the string we search for */
    if (len < 9)
        return -1;

    /* Make tmp point to the last char in the string */
    tmp = buf + len - 1;

    if (*tmp == 0)
        tmp--; /* Skip the \x00 at the end */

    /* Skip whitespaces at the end (if any) */
    while (isspace(*tmp))
    {
        tmp--;
        if (tmp == buf) /* Beginning of the buf */
            return -1;
    }

    /* Check that last non-whitespace character is digit */
    if (!isdigit(*tmp))
        return -1;

    tmp --;

    /* Scan all digits */
    while (isdigit(*tmp))
    {
        tmp--;
        if (tmp == buf) /* Beginning of the buf */
            return -1;
    }

    /* Check that before group of digits is whitespace character */
    if (!isspace(*tmp))
    {
        return -1;
    }

    /* Make a number point to the beginning of the group of numbers */
    number = tmp+1;

    tmp--;

    /* Skip whitespace characters */
    while (isspace(*tmp))
    {
        tmp--;
        if (tmp == buf) /* Beginning of the buf */
            return -1;
    }

    /* Check that more than 5+1 characters left */
    if ((tmp-buf) < 7)
        return -1;

    tmp -= 5;

    /* Is it 'attach' string ? */
    if (tmp[0] != 'a' ||
        tmp[1] != 't' ||
        tmp[2] != 't' ||
        tmp[3] != 'a' ||
        tmp[4] != 'c' ||
        tmp[5] != 'h')
    {
        /* No */
        return -1;
    }

    /* Insert ZERO before 'attach' word */
    tmp[-1] = 0;

    /* Convert string into the int and return the value */
    return atol(number);
}

/**
 * Read specified number of bytes (not less) from the connection
 *
 * @param socket        Connection socket.
 * @param buf           Buffer to store the data.
 * @param len           Number of bytes to read.
 *
 * @return
 *      Status code.
 *
 * @retval      0               Success.
 * @retval      other value     errno.
 */
static int
read_socket(int socket, char *buffer, size_t len)
{
    while (len > 0)
    {
        ssize_t r = recv(socket, buffer, len, 0);

        if (r <= 0)
        {
            return TE_OS_RC(TE_COMM, (r == 0) ? EPIPE : errno);
        }

        len -= r;
        buffer += r;
    }

    return 0;
}
