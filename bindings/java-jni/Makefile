all:
	cp ../corba/orbitcpp/webmgr.hpp jni/
	mkdir -p classes
	# build all classes and headers
	javac -h jni -d classes src/org/crosswire/android/sword/*.java
	javap -s -classpath classes/ org.crosswire.android.sword.SWMgr > SWMgr.txt
	javap -s -classpath classes/ org.crosswire.android.sword.SWMgr.ModInfo > ModInfo.txt
	javap -s -classpath classes/ org.crosswire.android.sword.SWModule > SWModule.txt
	javap -s -classpath classes/ org.crosswire.android.sword.SWModule.SearchHit > SearchHit.txt
	javap -s -classpath classes/ org.crosswire.android.sword.SWModule.SearchProgressReporter > SearchProgressReporter.txt
	javap -s -classpath classes/ org.crosswire.android.sword.InstallMgr > InstallMgr.txt
	# cp these things over to our Android JNI Project
	cp src/org/crosswire/android/sword/*.java ../Android/SWORD/app/src/main/java/org/crosswire/android/sword/
	ln -sf ../../../../../../../src/keys ../Android/SWORD/app/src/main/cpp/
	ln -sf ../../../../../../../src/utilfuns ../Android/SWORD/app/src/main/cpp/
	ln -sf ../../../../../../../src/mgr ../Android/SWORD/app/src/main/cpp/
	ln -sf ../../../../../../../src/modules ../Android/SWORD/app/src/main/cpp/
	ln -sf ../../../../../../../src/frontend ../Android/SWORD/app/src/main/cpp/
	ln -sf ../../../../../../java-jni/jni ../Android/SWORD/app/src/main/cpp/
	ln -sf ../../../../../../../../biblesync/src/ ../Android/SWORD/app/src/main/cpp/biblesync


clean:
	rm -rf jni/webmgr.hpp classes jni/org_crosswire_android_sword_*.h *.txt
