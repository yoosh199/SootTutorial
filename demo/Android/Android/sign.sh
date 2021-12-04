#!/bin/bash
BUILDTOOLS=$ANDROID_HOME/build-tools/30.0.2
zipalign=$BUILDTOOLS/zipalign.exe
apksigner=$BUILDTOOLS/apksigner.bat
INSTRUMENTED_APP=$1
KEY=$2
KEYSTORE_PASS=${3:-"android"}
TMP_FILE=/tmp/tmpfile.apk
PASS_OPT="--ks-pass pass:$KEYSTORE_PASS"
[[ -z "$KEYSTORE_PASS" ]] && PASS_OPT=""
$zipalign -f 4 $INSTRUMENTED_APP $TMP_FILE
$apksigner sign --ks $KEY  $PASS_OPT $TMP_FILE
cp $TMP_FILE $INSTRUMENTED_APP
rm $TMP_FILE
echo "The app is signed and located in $INSTRUMENTED_APP"
