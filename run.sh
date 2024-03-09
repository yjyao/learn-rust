#!/usr/bin/env bash

RED=$'\e[31m'
RESET=$'\e[0m'
chronic cargo --color always test &&
  cargo run ||
  echo -e "${RED}FAILED${RESET}"
