export LIB_NAME=literate-unitb-config
# git mv Z3/Version.hs config/Z3/Version.hs
# mkdir config
# mkdir config/Z3
git subtree split -P config -b simon/separate2-$LIB_NAME
cd ..
mkdir $LIB_NAME
cd $LIB_NAME
git init
git pull ../literate-unitb-logic simon/separate2-$LIB_NAME
cd ../$LIB_NAME
stack init --omit-packages
# export LIB_NAME=literate-unitb-scripts
# git subtree split -P script -b simon/separate-$LIB_NAME
# cd ..
# mkdir $LIB_NAME
# cd $LIB_NAME
# git init
# git pull ../literate-unitb simon/separate-$LIB_NAME
# cd ../$LIB_NAME
# stack init --omit-packages
