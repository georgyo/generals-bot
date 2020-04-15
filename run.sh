#!/usr/bin/env bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
pushd "$DIR" > /dev/null

poetry build --quiet --no-interaction
poetry run python -m generals_bot.bot_ek0x45 "${@}"
