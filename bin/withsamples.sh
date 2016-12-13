#!/bin/bash

usage="Usage: $0 [OPTIONS] -- COMMAND ARGS...

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
	;;
	(--)
	    cont=0
	    ;;
        (-h|--help)
	    echo $usage
	    exit 0
	    ;;
	(*)
	    echo Invalid argument: "$1"
	    echo $usage
	    exit 1
    esac
    shift
done

"$@" &
thatpid=$!
sleep $sleep
while kill -USR1 $thatpid
do
    sleep $sleep
done
