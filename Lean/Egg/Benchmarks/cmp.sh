#!/bin/bash

i=$1
cat detour | cut -d "," -f $i > d
cat original | cut -d "," -f $i > o
paste d o
