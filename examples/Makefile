
INCLUDEPATH = src


main: mutualEx2.ml german.ml g2k.ml flash_nodata_3.ml flash_nodata.ml flash_data.ml
	corebuild mutualEx2.byte -I ${INCLUDEPATH} -pkg re2
	corebuild g2k.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_nodata_cub.byte -I ${INCLUDEPATH} -pkg re2
	corebuild flash_data_cub.byte -I ${INCLUDEPATH} -pkg re2

clean:
	rm -rf _build
	rm *.byte
