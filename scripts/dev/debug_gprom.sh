#!/bin/bash
########################################
# VARS
# Directory this script resides in
pushd $(dirname "${0}") > /dev/null
DIR=$(pwd -L)
popd > /dev/null
# GProM binary
CONF_FILE=.gprom
GPROM=${DIR}/../../src/command_line/gprom
GPROM_CONF=${DIR}/../../${CONF_FILE}
########################################
# READ USER CONFIGUATION
source ${DIR}/../gprom_basic.sh
########################################
if [ $# -le 1 ]; then
	echo "Description: use lldb to debug gprom"
	echo " "
    echo "Usage: give at least two parameters, the first one is a loglevel, the second one is a query."
    echo "debug_gprom.sh 3 \"SELECT * FROM r;\""
    exit 1
fi

LLDB=lldb
GDB=gdb

LOG="-log -loglevel $1"
SQL=$2
ARGS="${*:3}"
SCRIPT=debug.script

echo "run ${CONNECTION_PARAMS} ${LOG} -treeify-algebra-graphs -sql \"${SQL}\" ${ARGS}" > ./$SCRIPT

# Mac or Linux
if [[ $OSTYPE == darwin* ]]; then
	${LLDB} -- ${GPROM} ${CONNECTION_PARAMS} ${LOG} -treeify-algebra-graphs -sql "${SQL}" ${ARGS}
else
	${GDB} ${GPROM} -x ./$SCRIPT
fi

#rm -f $SCRIPT
