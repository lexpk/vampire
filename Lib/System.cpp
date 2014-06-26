/**
 * @file System.cpp
 * Wrappers of some system functions and methods that take care of the
 * system stuff and don't fit anywhere else (handling signals etc...)
 */

#include "Portability.hpp"

#include <stdlib.h>
#if COMPILER_MSVC
#  include <Winsock2.h>
#  include <process.h>
#else
#  include <unistd.h>
#  if !__APPLE__
#    include <sys/prctl.h>
#  endif
#endif

#include <cerrno>
#include <string>
#include <csignal>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <fstream>

#include "Debug/Tracer.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"

#include "Environment.hpp"
#include "Exception.hpp"
#include "Int.hpp"
#include "Stack.hpp"
#include "Timer.hpp"

#include "System.hpp"

bool outputAllowed()
{
#if VDEBUG
  return true;
#else
  return !Lib::env || !Lib::env -> options || Lib::env -> options->mode()!=Shell::Options::MODE_SPIDER;
#endif
}

bool inSpiderMode()
{
  return Lib::env && Lib::env -> options && Lib::env -> options->mode()==Shell::Options::MODE_SPIDER;
}

void reportSpiderFail()
{
  reportSpiderStatus('!');
}

void reportSpiderStatus(char status)
{
  using namespace Lib;

  static bool headerPrinted=false;

  if(inSpiderMode() && !headerPrinted) {
    headerPrinted=true;

    env -> beginOutput();
    env -> out() << status << " "
      << (Lib::env -> options ? Lib::env -> options->problemName() : "unknown") << " "
      << (Lib::env -> timer ? Lib::env -> timer->elapsedDeciseconds() : 0) << " "
      << (Lib::env -> options ? Lib::env -> options->testId() : "unknown") << "\n";
    env -> endOutput();
  }
}

#if COMPILER_MSVC

#include <windows.h>

long long Lib::System::getSystemMemory()
{
  MEMORYSTATUSEX status;
  GlobalMemoryStatusEx(&status);
  return status.ullTotalPhys;
}

unsigned Lib::System::getNumberOfCores()
{
  SYSTEM_INFO sysinfo;
  GetSystemInfo( &sysinfo );
  return sysinfo.dwNumberOfProcessors;
}

#else

#include <unistd.h>

long long Lib::System::getSystemMemory()
{
#if __APPLE__
  NOT_IMPLEMENTED;
#else
  long pages = sysconf(_SC_PHYS_PAGES);
  long page_size = sysconf(_SC_PAGE_SIZE);
  return static_cast<long long>(pages) * page_size;
#endif
}

unsigned Lib::System::getNumberOfCores()
{
#if __APPLE__
  NOT_IMPLEMENTED;
#else
  return sysconf( _SC_NPROCESSORS_ONLN );
#endif
}


#endif

namespace Lib {

using namespace std;
using namespace Shell;

bool System::s_initialized = false;
bool System::s_shouldIgnoreSIGINT = false;
const char* System::s_argv0 = 0;

///**
// * Reimplements the system gethostname function.
// * @since 31/03/2005 Torrevieja
// */
//void System::gethostname(char* hostname,int maxlength)
//{
//  ::gethostname(hostname,maxlength);
//}

const char* signalToString (int sigNum)
{
  switch (sigNum)
    {
    case SIGTERM:
      return "SIGTERM";
# ifndef _MSC_VER
    case SIGQUIT:
      return "SIGQUIT";
    case SIGHUP:
      return "SIGHUP";
    case SIGXCPU:
      return "SIGXCPU";
    case SIGBUS:
      return "SIGBUS";
    case SIGTRAP:
      return "SIGTRAP";
# endif
    case SIGINT:
      return "SIGINT";
    case SIGILL:
      return "SIGILL";
    case SIGFPE:
      return "SIGFPE";
    case SIGSEGV:
      return "SIGSEGV";
    case SIGABRT:
      return "SIGABRT";
    default:
      return "UNKNOWN SIGNAL";
    }
} // signalToString


/**
 * Signal handling function. Rewritten from the kernel standalone.
 *
 * @param sigNum signal number
 * @since 28/06/2003 Manchester, statistics result registration added
 */
void handleSignal (int sigNum)
{
  // true if a terminal signal has been handled already.
  // to avoid catching signals over and over again
  static bool handled = false;
  static bool haveSigInt = false;
  const char* signalDescription = signalToString(sigNum);

  switch (sigNum)
    {
    case SIGTERM:
# ifndef _MSC_VER
    case SIGQUIT:
      if (handled) {
	System::terminateImmediately(haveSigInt ? VAMP_RESULT_STATUS_SIGINT : VAMP_RESULT_STATUS_OTHER_SIGNAL);
      }
      handled = true;
      if(outputAllowed()) {
	if(env -> options) {
	  env -> beginOutput();
	  env -> out() << "Aborted by signal " << signalDescription << " on " << env -> options->inputFile() << "\n";
	  env -> endOutput();
	} else {
	  cout << "Aborted by signal " << signalDescription << "\n";
	}
      }
      return;
    case SIGXCPU:
      if(outputAllowed()) {
	if(env -> options) {
	  env -> beginOutput();
	  env -> out() << "External time out (SIGXCPU) on " << env -> options->inputFile() << "\n";
	  env -> endOutput();
	} else {
	  cout << "External time out (SIGXCPU)\n";
	}
      }
      System::terminateImmediately(VAMP_RESULT_STATUS_OTHER_SIGNAL);
      break;
# endif

    case SIGINT:
      if(System::shouldIgnoreSIGINT()) {
	return;
      }
      haveSigInt=true;
//      exit(0);
//      return;

    case SIGILL:
    case SIGFPE:
    case SIGSEGV:

# ifndef _MSC_VER
    case SIGBUS:
    case SIGTRAP:
    case SIGHUP:
# endif
    case SIGABRT:
      {
	if (handled) {
	  System::terminateImmediately(haveSigInt ? VAMP_RESULT_STATUS_SIGINT : VAMP_RESULT_STATUS_OTHER_SIGNAL);
	}
	reportSpiderFail();
	handled = true;
	if(outputAllowed()) {
	  if(env -> options && env -> statistics) {
	    env -> beginOutput();
	    env -> out() << "Aborted by signal " << signalDescription << " on " << env -> options->inputFile() << "\n";
	    env -> statistics->print(env -> out());
#if VDEBUG
	    Debug::Tracer::printStack(env -> out());
#endif
	    env -> endOutput();
	  } else {
	    cout << "Aborted by signal " << signalDescription << "\n";
#if VDEBUG
	    Debug::Tracer::printStack(cout);
#endif
	  }
	}
	System::terminateImmediately(haveSigInt ? VAMP_RESULT_STATUS_SIGINT : VAMP_RESULT_STATUS_OTHER_SIGNAL);
      }

    default:
      break;
    }
} // handleSignal

void System::setSignalHandlers()
{
  signal(SIGTERM,handleSignal);
  signal(SIGINT,handleSignal);
  signal(SIGILL,handleSignal);
  signal(SIGFPE,handleSignal);
  signal(SIGSEGV,handleSignal);
  signal(SIGABRT,handleSignal);

#ifndef _MSC_VER
  signal(SIGQUIT,handleSignal);
  signal(SIGHUP,handleSignal);
  signal(SIGXCPU,handleSignal);
  signal(SIGBUS,handleSignal);
  signal(SIGTRAP,handleSignal);
#endif

  errno=0;
  int res=atexit(onTermination);
  if(res==-1) {
    SYSTEM_FAIL("Call of atexit() function in System::setSignalHandlers failed.", errno);
  }
  ASS_EQ(res,0);
}

/**
 * Function that returns a reference to an array that contains
 * lists of initialization handlers
 *
 * Using a function with a static variable inside is a way to ensure
 * that no matter how early we want to register an initialization
 * handler, the array will be constructed.
 */
ZIArray<List<VoidFunc>*>& System::initializationHandlersArray()
{
  CALL("System::initializationHandlersArray");

  static ZIArray<List<VoidFunc>*> arr;
  return arr;
}

/**
 * Ensure that @b proc will be called after all static variables are
 * initialized, but before the @b main() function.
 * Functions added with higher @b priority will be called first.
 */
void System::addInitializationHandler(VoidFunc proc, unsigned priority)
{
  CALL("System::addInitializationHandler");

  if(s_initialized) {
    proc();
  }
  else {
    VoidFuncList::push(proc, initializationHandlersArray()[priority]);
  }
}

/**
 * This function should be called as the last thing on every path that leads
 * to a process termination.
 */
void System::onInitialization()
{
  CALL("System::onTermination");
  ASS(!s_initialized); //onInitialization can be called only once

  s_initialized=true;

  int sz=initializationHandlersArray().size();
  for(int i=sz-1;i>=0;i--) {
    VoidFuncList::Iterator ihIter(initializationHandlersArray()[i]);
    while(ihIter.hasNext()) {
      VoidFunc func=ihIter.next();
      func();
    }
  }
}

/**
 * Ensure that @b proc will be called before termination of the process.
 * Functions added with lower @b priority will be called first.
 *
 * We try to cover all possibilities how the process may terminate, but
 * some are probably impossible (such as receiving the signal 9). In these
 * cases the @b proc function is not called.
 */
void System::addTerminationHandler(VoidFunc proc, unsigned priority)
{
  CALL("System::addTerminationHandler");

  VoidFuncList::push(proc, s_terminationHandlers[priority]);
}

/**
 * This function should be called as the last thing on every path that leads
 * to a process termination.
 */
void System::onTermination()
{
  CALL("System::onTermination");

  static bool called=false;
  if(called) {
    return;
  }
  called=true;

  size_t sz=s_terminationHandlers.size();
  for(size_t i=0;i<sz;i++) {
    VoidFuncList::Iterator thIter(s_terminationHandlers[i]);
    while(thIter.hasNext()) {
      VoidFunc func=thIter.next();
      func();
    }
  }
}

void System::terminateImmediately(int resultStatus)
{
  CALL("System::terminateImmediately");

  onTermination();
  _exit(resultStatus);
}

/**
 * Make sure that the process will receive the SIGHUP signal
 * when its parent process dies
 *
 * This setting is not passed to the child precesses created by fork().
 */
void System::registerForSIGHUPOnParentDeath()
{
#if __APPLE__ || COMPILER_MSVC
  cerr<<"Death of parent process not being handled on Mac and Windows"<<endl;
//  NOT_IMPLEMENTED;
#else
  prctl(PR_SET_PDEATHSIG, SIGHUP);
#endif
}

/**
 * Read command line arguments into @c res and register the executable name
 * (0-th element of @c argv) using the @c registerArgv0() function.
 */
void System::readCmdArgs(int argc, char* argv[], StringStack& res)
{
  CALL("System::readCmdArgs");
  ASS_GE(argc,1);
  ASS(res.isEmpty()); //just to avoid any confusion, if it causes problems, the assumption can be removed

  registerArgv0(argv[0]);
  for(int i=1; i<argc; i++) {
    res.push(argv[i]);
  }
}

string System::extractFileNameFromPath(string str)
{
  CALL("System::extractFileNameFromPath");

  size_t index=str.find_last_of("\\/")+1;
  if(index==string::npos) {
    return str;
  }
  return string(str, index);
}

/**
 * If directory name can be extracted from @c path, assign it into
 * @c dir and return true; otherwise return false.
 *
 * The directory name is extracted without the final '/'.
 */
bool System::extractDirNameFromPath(string path, string& dir)
{
  CALL("System::extractDirNameFromPath");

  size_t index=path.find_last_of("\\/");
  if(index==string::npos) {
    return false;
  }
  dir = path.substr(0, index);
  return true;
}

bool System::fileExists(string fname)
{
  CALL("System::fileExists");

  ifstream ifile(fname.c_str());
  return ifile;
}

/**
 * Guess path to the current executable.
 *
 * Guessing means that the returned path might not be correct.
 */
string System::guessExecutableDirectory()
{
  CALL("System::guessExecutableDirectory");

  string res;

  if(s_argv0 && extractDirNameFromPath(s_argv0, res)) {
    return res;
  }

  return ".";
}

/**
 * Guess the current executable file.
 *
 * Guessing means that the returned file path might not be correct.
 */
string System::guessExecutableName()
{
  CALL("System::guessExecutableName");

  string res;

  if(s_argv0) {
    return s_argv0;
  }

  return "./vampire";
}

pid_t System::getPID()
{
  CALL("System::getPID");

#if !COMPILER_MSVC
  return getpid();
#else
  //TODO: Implement pid retrieval for windows
  return 0;
#endif
}

/**
 * Execute command @c command, pass content of @c input as standard input
 * and return the output of the command in @c output.
 */
int System::executeCommand(string command, string input, Stack<string>& outputLines)
{
  CALL("System::executeCommand");

#if COMPILER_MSVC
  NOT_IMPLEMENTED;
#else
  string pidStr = Int::toString(getPID());
  string inFile  = "/tmp/vampire_executeCommand_"+pidStr+"_in";
  string outFile = "/tmp/vampire_executeCommand_"+pidStr+"_out";

  string cmdLine = command + " <" + inFile + " >" + outFile;

  {
    ofstream inpFile(inFile.c_str());
    inpFile << input;
    inpFile.close();
  }

  int resStatus=system(cmdLine.c_str());

  {
    outputLines.reset();
    string line;
    ifstream outpFile(outFile.c_str());
    while (getline(outpFile, line)) {
      outputLines.push(line);
    }
    outpFile.close();
  }

//  if(WIFSIGNALED(resStatus) && WTERMSIG(resStatus)==SIGINT) {
//    //if child Vampire was terminated by SIGINT (Ctrl+C), we also terminate
//    //(3 is the return value for this case; see documentation for the
//    //@b vampireReturnValue global variable)
//    handleSIGINT();
//  }

  remove(inFile.c_str());
  remove(outFile.c_str());

  if(WIFEXITED(resStatus)) {
    return WEXITSTATUS(resStatus);
  }
  else if(WIFSIGNALED(resStatus)) {
    return -WTERMSIG(resStatus);
  }
  else {
    return -0xffff;
  }

#endif
}

};
