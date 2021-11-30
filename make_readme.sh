#!/bin/sh

cd bitpatterns \
&& cargo readme > README.md \
&& cp README.md .. \
&& cd .. \
&& cd bitpatterns-proc-macro \
&& cargo readme > README.md \
&& cd ..
