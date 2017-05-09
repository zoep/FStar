#!/bin/bash

prefix=${prefix:-/usr/local}

install -m 0755 bin/fstar.exe ${prefix}/bin/fstar
install -m 0644 scripts/fstar_completion /etc/bash_completion.d/fstar
