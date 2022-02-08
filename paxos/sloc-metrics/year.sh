csv_files=(`find $ROOT_DIR *.csv`)


for cf in "${csv_files[@]}"
do :
    echo $cf
    prefix=$( echo $cf | cut -c1-9 )
    suffix=$( echo $cf | cut -c10- )

    if [[ "$prefix" =~ .*"Jan".* ]]; then 
        new_name="$prefix-2022$suffix"
    else
        new_name="$prefix-2021$suffix"
    fi
    mv $cf $new_name
done