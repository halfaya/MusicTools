/*
 * MusicTools MuseScore test plugin
 */

import QtQuick 2.0
import MuseScore 3.0

MuseScore {
    menuPath: "Plugins.run"
    version:  "3.0"
    description: "This demo plugin runs an external command."
    requiresScore: false

    QProcess {
        id: proc
    }

    onRun: {
        proc.start("/Users/leo/github/MusicTools/agda/Main")
        var val = proc.waitForFinished(30000);
        if (val) {
          console.log(proc.readAllStandardOutput());
        }
        console.log("done");
        Qt.quit()
    }
}
