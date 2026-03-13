LOCAL_PATH := $(call my-dir)

include $(CLEAR_VARS)
LOCAL_MODULE        := PlayerTracker
LOCAL_SRC_FILES     := main.cpp
LOCAL_CPPFLAGS      := -std=c++17 -O2 -fvisibility=hidden -fexceptions -frtti
LOCAL_LDLIBS        := -llog -lEGL -lGLESv2 -landroid -ldl
include $(BUILD_SHARED_LIBRARY)
