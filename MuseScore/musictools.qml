/*
 * MusicTools MuseScore test plugin
 */

import QtQuick 2.0
import MuseScore 3.0

MuseScore {
    menuPath: "Plugins.musictools"
    version:  "3.0"
    description: "Test of integration with MusicTools."

    QProcess {
        id: proc
    }

    onRun: {
    /*
        proc.start("/Users/leo/github/MusicTools/agda/Main")
        var val = proc.waitForFinished(30000);
        if (val) {
         console.log(proc.readAllStandardOutput());
       }
    */
        var cursor = curScore.newCursor();
        cursor.rewind(Cursor.SCORE_START);
        while (cursor.segment) {
            if (cursor.element && cursor.element.type === Element.CHORD) {
                var notes = cursor.element.notes;
                for (var k = 0; k < notes.length; k++) {
                    //console.log(notes[k].noteType + " " + notes[k].pitch);
                    //text.text = notes[k].pitch % 12;
                    proc.start("/Users/leo/github/MusicTools/agda/Main " + notes[k].pitch);
                    var val = proc.waitForFinished();
                    if (val) {
                        var text = newElement(Element.STAFF_TEXT);      // Make a STAFF_TEXT
                        text.text = proc.readAllStandardOutput();
                        cursor.add(text);
                    }
                }
            }
            cursor.next();
        }
        console.log("done");
        Qt.quit()
    }
}
