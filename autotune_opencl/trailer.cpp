/*
Collect information from multiple .trails
@author Sergey Staroletov serg_soft@mail.ru https://www.researchgate.net/profile/Sergey_Staroletov
@author Natalia Garanina natta.garanina@gmail.com https://www.researchgate.net/profile/Natalia-Garanina
@conference LOPSTR-2022
@license GNU GPL
*/
#include <QCoreApplication>
#include <QDir>
#include <QList>
#include <QProcess>
#include <QtAlgorithms>

struct rec {
  int time;
  int TS;
  int WG;
  int steps;
  QString tail;
};

int main(int argc, char *argv[]) {
  QCoreApplication app(argc, argv);

  QString rootDir = qApp->applicationDirPath();
  QDir test(rootDir);
  QStringList testlist = test.entryList();
  QString spin = "/usr/local/bin/spin";
  QList<rec> rec_data;
  int total = 0;

  //find all .trail files
  for (auto &path : testlist)
    if (path.indexOf(".trail") > 0) {
      // run spin in simulation mode for it
      QProcess p;
      QStringList params;
      params << "-k";
      params << "./" + path;
      params << "./autotune.pml";
      p.start(spin, params);
      p.waitForFinished();
      // read its output
      QString out = p.readAll();
      QStringList lines = out.split("\n");

      // prepare a record for it
      rec rec_d;
      rec_d.time = 0;
      rec_d.steps = 0;
      // collect parameters from the output
      for (auto &line : lines) {
        int i = line.indexOf("time = ");
        if (i > 0) rec_d.time = line.mid(i + 7).simplified().toInt();
        i = line.indexOf("TS = ");
        if (i > 0) rec_d.TS = line.mid(i + 5).simplified().toInt();
        i = line.indexOf("WG = ");
        if (i > 0) rec_d.WG = line.mid(i + 5).simplified().toInt();
        i = line.indexOf("ends after");
        int is = line.indexOf("steps");
        if (i > 0 && is > 0)
          rec_d.steps =
              line.mid(i + 11).simplified().mid(0, is - i - 11).toInt();
      }
      rec_d.tail = path;
      if (rec_d.time > 0) {
        rec_data.append(rec_d);
        total++;
      }
    }
  // sort it by time then number of steps
  struct {
    bool operator()(rec a, rec b) const {
      if (a.time != b.time)
        return a.time < b.time;
      else
        return a.steps < b.steps;
    }
  } customLess;
  std::sort(rec_data.begin(), rec_data.end(), customLess);

  //print it out
  for (int i = 0; i < total; i++) {
    printf("(time = %d  TS = %d  WG = %d steps = %d path = %s )\n",
           rec_data[i].time, rec_data[i].TS, rec_data[i].WG, rec_data[i].steps,
           rec_data[i].tail.toStdString().c_str());
  }

  return 0;
}
