#!/bin/bash

cat $1 | sed '/^[[:space:]]*$/d'

