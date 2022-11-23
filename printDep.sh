#!/bin/bash

dep=$(coqdep -sort -Q src PlutusCert ./src)
deps=($dep)

echo "-Q src PlutusCert"

for i in "${deps[@]}"
do
  echo $i
done
