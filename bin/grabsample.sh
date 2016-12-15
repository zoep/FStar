#!/bin/bash

usage="Usage: $0 [OPTIONS] PID

OPTIONS are:

-h,--help           Print this message
--sleep <interval>  Sleeps <interval> seconds between each snapshot
"

sleep=0.1

cont=1
while [ $cont -ne 0 ] && [ -n "$1" ]
do
    case "$1" in
	(--sleep)
	    shift
	    sleep="$1"
	    shift
	;;
        (-h|--help)
	    echo $usage
	    exit 0
	    ;;
	(*)
	    cont=0
    esac
done

thatpid=$1
while kill -USR1 $thatpid
do
    sleep $sleep
done
