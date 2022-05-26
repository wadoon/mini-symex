double round_up(double value, int digits) {
  assert(digits < 3);
  double ret = 0;
  if (digits == 0) {
    ret = (double)((int)value + 1);
  } else if (digits == 1) {
    ret = (double)(int)(10 * value + 1) / 10;
  } else if (digits == 2) {
    ret = (double)(int)(100 * value + 1) / 100;
  }
  return ret;
}

double round_down(double value, int digits) {
  assert(digits < 3);
  double ret = 0;
  if (digits == 0) {
    ret = (double)((int)value);
  } else if (digits == 1) {
    ret = (double)(int)(10 * value) / 10;
  } else if (digits == 2) {
    ret = (double)(int)(100 * value) / 100;
  }
  return ret;
}

void MPARA();
void MRE4JL();
void MSOLZSTS();
void MRE4();
void MRE4ABZ();
void MBERECH();
void MSONST();
void MVMT();
void MOSONST();
void STSMIN();
void MRE4SONST();
void UPANTEIL();
void MSOLZ();
void UPTAB22();
void UP5_6();
void MST5_6();
void MVSP();
void UPEVP();
void UPTAB22();
void UPMLST();
void UPLSTLZZ();
void UPVKV();
void UPVKVLZZ();
void MZTABFB();
void MLSTJAHR();
void MLSTJAHR();
void MZTABFB();
void MRE4ALTE();

/*  Stand: 2021-11-09 10:25 */
/*  ITZBund Berlin  */
/*   EINGABEPARAMETER   */

/*  1, wenn die Anwendung des Faktorverfahrens gewählt wurden (nur in
 * Steuerklasse IV)  */
int af = 1;
/*  Auf die Vollendung des 64. Lebensjahres folgende
                     Kalenderjahr (erforderlich, wenn ALTER1=1)  */
int AJAHR;
/*  1, wenn das 64. Lebensjahr zu Beginn des Kalenderjahres vollendet wurde, in
   dem der Lohnzahlungszeitraum endet (§ 24 a EStG), sonst = 0  */
int ALTER1;
/*  in VKAPA und VMT enthaltene Entschädigungen nach §24 Nummer 1 EStG
                     sowie tarifermäßigt zu besteuernde Vorteile bei
   Vermögensbeteiligungen (§ 19a Absatz 4 EStG) in Cent  */
double ENTSCH = (double)0;
/*  eingetragener Faktor mit drei Nachkommastellen  */
double f = 1.0;
/*  Jahresfreibetrag für die Ermittlung der Lohnsteuer für die sonstigen Bezüge
                     sowie für Vermögensbeteiligungen nach § 19a Absatz 1 und 4
   EStG nach Maßgabe der elektronischen Lohnsteuerabzugsmerkmale nach § 39e EStG
   oder der Eintragung auf der Bescheinigung für den Lohnsteuerabzug 2022 in
   Cent (ggf. 0)  */
double JFREIB;
/*  Jahreshinzurechnungsbetrag für die Ermittlung der Lohnsteuer für die
   sonstigen Bezüge sowie für Vermögensbeteiligungen nach § 19a Absatz 1 und 4
   EStG nach Maßgabe der elektronischen Lohnsteuerabzugsmerkmale nach § 39e EStG
   oder der Eintragung auf der Bescheinigung für den Lohnsteuerabzug 2022 in
   Cent (ggf. 0)  */
double JHINZU;
/*  Voraussichtlicher Jahresarbeitslohn ohne sonstige Bezüge (d.h. auch ohne
   Vergütung für mehrjährige Tätigkeit und ohne die zu besteuernden Vorteile bei
   Vermögensbeteiligungen, § 19a Absatz 4 EStG) in Cent. Anmerkung: Die Eingabe
   dieses Feldes (ggf. 0) ist erforderlich bei Eingaben zu sonstigen Bezügen
   (Felder SONSTB, VMT oder VKAPA). Sind in einem vorangegangenen
   Abrechnungszeitraum bereits sonstige Bezüge gezahlt worden, so sind sie dem
   voraussichtlichen Jahresarbeitslohn hinzuzurechnen. Gleiches gilt für zu
                     besteuernde Vorteile bei Vermögensbeteiligungen (§ 19a
   Absatz 4 EStG). Vergütungen für mehrjährige Tätigkeit aus einem
   vorangegangenen Abrechnungszeitraum werden in voller Höhe hinzugerechnet. */
double JRE4;
/*  In JRE4 enthaltene Versorgungsbezuege in Cents (ggf. 0)  */
double JVBEZ;
/* Merker für die Vorsorgepauschale
                                2 = der Arbeitnehmer ist NICHT in der
   gesetzlichen Rentenversicherung versichert.

                                1 = der Arbeitnehmer ist in der gesetzlichen
   Rentenversicherung versichert, es gilt die Beitragsbemessungsgrenze OST.

                                0 = der Arbeitnehmer ist in der gesetzlichen
   Rentenversicherung versichert, es gilt die Beitragsbemessungsgrenze WEST.  */
int KRV;
/*  Einkommensbezogener Zusatzbeitragssatz eines gesetzlich krankenversicherten
   Arbeitnehmers, auf dessen Basis der an die Krankenkasse zu zahlende
   Zusatzbeitrag berechnet wird, in Prozent (bspw. 0,90 für 0,90 %) mit 2
   Dezimalstellen.
                         Der von der Kranken-kasse festgesetzte
   Zusatzbeitragssatz ist bei Abweichungen unmaßgeblich.  */
double KVZ;
/*  Lohnzahlungszeitraum:
                     1 = Jahr
                     2 = Monat
                     3 = Woche
                     4 = Tag  */
int LZZ;
/*  Der als elektronisches Lohnsteuerabzugsmerkmal für den Arbeitgeber nach §
   39e EStG festgestellte oder in der Bescheinigung für den Lohnsteuerabzug 2022
   eingetragene Freibetrag für den Lohnzahlungszeitraum in Cent  */
double LZZFREIB;
/*  Der als elektronisches Lohnsteuerabzugsmerkmal für den Arbeitgeber nach §
   39e EStG festgestellte oder in der Bescheinigung für den Lohnsteuerabzug 2022
   eingetragene Hinzurechnungsbetrag für den Lohnzahlungszeitraum in Cent  */
double LZZHINZU;
/*  Nicht zu besteuernde Vorteile bei Vermögensbeteiligungen
                     (§ 19a Absatz 1 Satz 4 EStG) in Cent  */
double MBV;
/*  Dem Arbeitgeber mitgeteilte Zahlungen des Arbeitnehmers zur privaten
                     Kranken- bzw. Pflegeversicherung im Sinne des §10 Abs. 1
   Nr. 3 EStG 2010 als Monatsbetrag in Cent (der Wert ist inabhängig vom
   Lohnzahlungszeitraum immer als Monatsbetrag anzugeben). */
double PKPV = (double)0;
/*  Krankenversicherung:
                     0 = gesetzlich krankenversicherte Arbeitnehmer
                     1 = ausschließlich privat krankenversicherte Arbeitnehmer
   OHNE Arbeitgeberzuschuss 2 = ausschließlich privat krankenversicherte
   Arbeitnehmer MIT Arbeitgeberzuschuss  */
int PKV = 0;
/*  1, wenn bei der sozialen Pflegeversicherung die Besonderheiten in Sachsen zu
   berücksichtigen sind bzw. zu berücksichtigen wären, sonst 0.  */
int PVS = 0;
/*  1, wenn er der Arbeitnehmer den Zuschlag zur sozialen Pflegeversicherung
                                zu zahlen hat, sonst 0.  */
int PVZ = 0;
/*  Religionsgemeinschaft des Arbeitnehmers lt. elektronischer
   Lohnsteuerabzugsmerkmale oder der
                     Bescheinigung für den Lohnsteuerabzug 2022 (bei keiner
   Religionszugehörigkeit = 0)  */
int R;
/*  Steuerpflichtiger Arbeitslohn für den Lohnzahlungszeitraum vor
   Berücksichtigung des Versorgungsfreibetrags und des Zuschlags zum
   Versorgungsfreibetrag, des Altersentlastungsbetrags und des als
   elektronisches Lohnsteuerabzugsmerkmal festgestellten oder in der
   Bescheinigung für den Lohnsteuerabzug 2022 für den Lohnzahlungszeitraum
   eingetragenen Freibetrags bzw. Hinzurechnungsbetrags in Cent  */
double RE4;
/*  Sonstige Bezüge (ohne Vergütung aus mehrjähriger Tätigkeit) einschließlich
   nicht tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen und
   Sterbegeld bei Versorgungsbezügen sowie Kapitalauszahlungen/Abfindungen,
   soweit es sich nicht um Bezüge für mehrere Jahre handelt, in Cent (ggf. 0) */
double SONSTB;
/*  Sterbegeld bei Versorgungsbezuegen sowie Kapitalauszahlungen/Abfindungen,
                     soweit es sich nicht um Bezuege fuer mehrere Jahre handelt
                     (in SONSTB enthalten) in Cents  */
double STERBE;
/*  Steuerklasse:
                     1 = I
                     2 = II
                     3 = III
                     4 = IV
                     5 = V
                     6 = VI  */
int STKL;
/*  In RE4 enthaltene Versorgungsbezuege in Cents (ggf. 0)  */
double VBEZ;
/*  Vorsorgungsbezug im Januar 2005 bzw. fuer den ersten vollen Monat
                     in Cents */
double VBEZM;
/*  Voraussichtliche Sonderzahlungen im Kalenderjahr des Versorgungsbeginns
                     bei Versorgungsempfaengern ohne Sterbegeld,
   Kapitalauszahlungen/Abfindungen bei Versorgungsbezuegen in Cents */
double VBEZS;
/*  In SONSTB enthaltene Versorgungsbezuege einschliesslich Sterbegeld
                    in Cents (ggf. 0)  */
double VBS;
/*  Jahr, in dem der Versorgungsbezug erstmalig gewaehrt wurde; werden
                     mehrere Versorgungsbezuege gezahlt, so gilt der aelteste
   erstmalige Bezug  */
int VJAHR;
/*  Kapitalauszahlungen / Abfindungen / Nachzahlungen bei Versorgungsbezügen
                     für mehrere Jahre in Cent (ggf. 0)  */
double VKAPA;
/*  Entschädigungen und Vergütung für mehrjährige Tätigkeit sowie tarifermäßigt
                             zu besteuernde Vorteile bei Vermögensbeteiligungen
   (§ 19a Absatz 4 Satz 2 EStG) ohne Kapitalauszahlungen und ohne Abfindungen
   bei Versorgungsbezügen in Cent (ggf. 0)  */
double VMT;
/*  Zahl der Freibetraege fuer Kinder (eine Dezimalstelle, nur bei Steuerklassen
                     I, II, III und IV)  */
double ZKF;
/*  Zahl der Monate, fuer die Versorgungsbezuege gezahlt werden (nur
                     erforderlich bei Jahresberechnung (LZZ = 1)  */
int ZMVB;
/*  In JRE4 enthaltene Entschädigungen nach § 24 Nummer 1 EStG und zu
   besteuernde
                     Vorteile bei Vermögensbeteiligungen (§ 19a Absatz 4 EStG in
   Cent  */
double JRE4ENT = 0.0;
/*  In SONSTB enthaltene Entschädigungen nach § 24 Nummer 1 EStG sowie nicht
                     tarifermäßigt zu besteuernde Vorteile bei
   Vermögensbeteiligungen in Cent  */
double SONSTENT = 0.0;

/*   AUSGABEPARAMETER   */

/*  Bemessungsgrundlage fuer die Kirchenlohnsteuer in Cents  */
double BK = (double)0;
/*  Bemessungsgrundlage der sonstigen Bezüge (ohne Vergütung für mehrjährige
   Tätigkeit) für die Kirchenlohnsteuer in Cent. Hinweis: Negativbeträge, die
   aus nicht zu besteuernden Vorteilen bei Vermögensbeteiligungen (§ 19a Absatz
   1 Satz 4 EStG) resultieren, mindern BK (maximal bis 0). Der
   Sonderausgabenabzug für tatsächlich erbrachte Vorsorgeaufwendungen
                 im Rahmen der Veranlagung zur Einkommensteuer bleibt unberührt.
 */
double BKS = (double)0;
/*  Bemessungsgrundlage der Vergütung für mehrjährige Tätigkeit und der
   tarifermäßigt zu besteuernden Vorteile bei Vermögensbeteiligungen für die
   Kirchenlohnsteuer in Cent   */
double BKV = (double)0;
/*  Fuer den Lohnzahlungszeitraum einzubehaltende Lohnsteuer in Cents  */
double LSTLZZ = (double)0;
/*  Fuer den Lohnzahlungszeitraum einzubehaltender Solidaritaetszuschlag
                     in Cents  */
double SOLZLZZ = (double)0;
/*  Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige
   Tätigkeit in Cent. Hinweis: Negativbeträge, die aus nicht zu besteuernden
   Vorteilen bei Vermögensbeteiligungen (§ 19a Absatz 1 Satz 4 EStG)
   resultieren, mindern SOLZLZZ (maximal bis 0). Der Sonderausgabenabzug für
   tatsächlich erbrachte Vorsorgeaufwendungen im Rahmen der Veranlagung zur
   Einkommensteuer bleibt unberührt.  */
double SOLZS = (double)0;
/*  Solidaritätszuschlag für die Vergütung für mehrjährige Tätigkeit und der
   tarifermäßigt zu besteuernden Vorteile bei Vermögensbeteiligungen in Cent  */
double SOLZV = (double)0;
/*  Lohnsteuer für sonstige Bezüge (ohne Vergütung für mehrjährige Tätigkeit und
   ohne tarifermäßigt zu besteuernde Vorteile bei Vermögensbeteiligungen) in
   Cent Hinweis: Negativbeträge, die aus nicht zu besteuernden Vorteilen bei
   Vermögensbeteiligungen (§ 19a Absatz 1 Satz 4 EStG) resultieren, mindern
   LSTLZZ (maximal bis 0). Der Sonderausgabenabzug für tatsächlich erbrachte
   Vorsorgeaufwendungen im Rahmen der Veranlagung zur Einkommensteuer bleibt
   unberührt.  */
double STS = (double)0;
/*  Lohnsteuer für die Vergütung für mehrjährige Tätigkeit und der tarifermäßigt
   zu besteuernden Vorteile bei Vermögensbeteiligungen in Cent  */
double STV = (double)0;
/*  Für den Lohnzahlungszeitraum berücksichtigte Beiträge des Arbeitnehmers zur
                                 privaten Basis-Krankenversicherung und privaten
   Pflege-Pflichtversicherung (ggf. auch die Mindestvorsorgepauschale) in Cent
   beim laufenden Arbeitslohn. Für Zwecke der Lohn- steuerbescheinigung sind die
   einzelnen Ausgabewerte außerhalb des eigentlichen Lohn-
                                 steuerbescheinigungsprogramms zu addieren;
   hinzuzurechnen sind auch die Ausgabewerte VKVSONST  */
double VKVLZZ = (double)0;
/*  Für den Lohnzahlungszeitraum berücksichtigte Beiträge des Arbeitnehmers
                                 zur privaten Basis-Krankenversicherung und
   privaten Pflege-Pflichtversicherung (ggf. auch die Mindestvorsorgepauschale)
   in Cent bei sonstigen Bezügen. Der Ausgabewert kann auch negativ sein. Für
   tarifermäßigt zu besteuernde Vergütungen für mehrjährige
                                 Tätigkeiten enthält der PAP keinen
   entsprechenden Ausgabewert.  */
double VKVSONST = (double)0;

/*   AUSGABEPARAMETER DBA   */

/*  Verbrauchter Freibetrag bei Berechnung des laufenden Arbeitslohns, in Cent
 */
double VFRB = (double)0;
/*  Verbrauchter Freibetrag bei Berechnung des voraussichtlichen
 * Jahresarbeitslohns, in Cent  */
double VFRBS1 = (double)0;
/*  Verbrauchter Freibetrag bei Berechnung der sonstigen Bezüge, in Cent  */
double VFRBS2 = (double)0;
/*  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA
   Türkei verfügbares ZVE über dem Grundfreibetrag bei der Berechnung des
   laufenden Arbeitslohns, in Cent  */
double WVFRB = (double)0;
/*  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA
   Türkei verfügbares ZVE über dem Grundfreibetrag bei der Berechnung des
   voraussichtlichen Jahresarbeitslohns, in Cent  */
double WVFRBO = (double)0;
/*  Für die weitergehende Berücksichtigung des Steuerfreibetrags nach dem DBA
   Türkei verfügbares ZVE über dem Grundfreibetrag bei der Berechnung der
   sonstigen Bezüge, in Cent  */
double WVFRBM = (double)0;

/*   INTERNE FELDER   */

/*  Altersentlastungsbetrag nach Alterseinkünftegesetz in €,
                             Cent (2 Dezimalstellen)  */
double ALTE = (double)0;
/*  Arbeitnehmer-Pauschbetrag in EURO  */
double ANP = (double)0;
/*  Auf den Lohnzahlungszeitraum entfallender Anteil von Jahreswerten
                             auf ganze Cents abgerundet  */
double ANTEIL1 = (double)0;
/*  Bemessungsgrundlage für Altersentlastungsbetrag in €, Cent
                             (2 Dezimalstellen)  */
double BMG = (double)0;
/*  Beitragsbemessungsgrenze in der gesetzlichen Krankenversicherung
                                und der sozialen Pflegeversicherung in Euro  */
double BBGKVPV = (double)0;
/*   Nach Programmablaufplan 2019  */
double bd = (double)0;
/*  allgemeine Beitragsbemessungsgrenze in der allgemeinen Renten-versicherung
 * in Euro  */
double BBGRV = (double)0;
/*  Differenz zwischen ST1 und ST2 in EURO  */
double DIFF = (double)0;
/*  Entlastungsbetrag für Alleinerziehende in Euro
                             Hinweis: Der Entlastungsbetrag für Alleinerziehende
   beträgt ab 2022 4.008 Euro. Der Erhöhungsbetrag von 2.100 Euro, der für die
                             Jahre 2020 und 2021 galt, ist ab 2022 weggefallen
   (Jahressteuergesetz 2020).  */
double EFA = (double)0;
/*  Versorgungsfreibetrag in €, Cent (2 Dezimalstellen)  */
double FVB = (double)0;
/*  Versorgungsfreibetrag in €, Cent (2 Dezimalstellen) für die Berechnung
                             der Lohnsteuer für den sonstigen Bezug  */
double FVBSO = (double)0;
/*  Zuschlag zum Versorgungsfreibetrag in EURO  */
double FVBZ = (double)0;
/*  Zuschlag zum Versorgungsfreibetrag in EURO fuer die Berechnung
                             der Lohnsteuer beim sonstigen Bezug  */
double FVBZSO = (double)0;
/*  Grundfreibetrag in Euro  */
double GFB = (double)0;
/*  Maximaler Altersentlastungsbetrag in €  */
double HBALTE = (double)0;
/*  Massgeblicher maximaler Versorgungsfreibetrag in €  */
double HFVB = (double)0;
/*  Massgeblicher maximaler Zuschlag zum Versorgungsfreibetrag in €,Cent
                             (2 Dezimalstellen)  */
double HFVBZ = (double)0;
/*  Massgeblicher maximaler Zuschlag zum Versorgungsfreibetrag in €, Cent
                             (2 Dezimalstellen) für die Berechnung der
   Lohnsteuer für den sonstigen Bezug  */
double HFVBZSO = (double)0;
/*  Nummer der Tabellenwerte fuer Versorgungsparameter  */
int J = 0;
/*  Jahressteuer nach § 51a EStG, aus der Solidaritaetszuschlag und
                             Bemessungsgrundlage fuer die Kirchenlohnsteuer
   ermittelt werden in EURO  */
double JBMG = (double)0;
/*  Auf einen Jahreslohn hochgerechneter LZZFREIB in €, Cent
                             (2 Dezimalstellen)  */
double JLFREIB = (double)0;
/*  Auf einen Jahreslohn hochgerechnete LZZHINZU in €, Cent
                             (2 Dezimalstellen)  */
double JLHINZU = (double)0;
/*  Jahreswert, dessen Anteil fuer einen Lohnzahlungszeitraum in
                             UPANTEIL errechnet werden soll in Cents  */
double JW = (double)0;
/*  Nummer der Tabellenwerte fuer Parameter bei Altersentlastungsbetrag  */
int K = 0;
/*  Merker für Berechnung Lohnsteuer für mehrjährige Tätigkeit.
                                         0 = normale Steuerberechnung
                                         1 = Steuerberechnung für mehrjährige
   Tätigkeit 2 = entfällt  */
int KENNVMT = 0;
/*  Summe der Freibetraege fuer Kinder in EURO  */
double KFB = (double)0;
/*  Beitragssatz des Arbeitgebers zur Krankenversicherung  */
double KVSATZAG = (double)0;
/*  Beitragssatz des Arbeitnehmers zur Krankenversicherung  */
double KVSATZAN = (double)0;
/*  Kennzahl fuer die Einkommensteuer-Tabellenart:
                             1 = Grundtabelle
                             2 = Splittingtabelle  */
int KZTAB = 0;
/*  Jahreslohnsteuer in EURO  */
double LSTJAHR = (double)0;
/*  Zwischenfelder der Jahreslohnsteuer in Cent  */
double LST1 = (double)0;
double LST2 = (double)0;
double LST3 = (double)0;
double LSTOSO = (double)0;
double LSTSO = (double)0;
/*  Mindeststeuer fuer die Steuerklassen V und VI in EURO  */
double MIST = (double)0;
/*  Beitragssatz des Arbeitgebers zur Pflegeversicherung  */
double PVSATZAG = (double)0;
/*  Beitragssatz des Arbeitnehmers zur Pflegeversicherung  */
double PVSATZAN = (double)0;
/*  Beitragssatz des Arbeitnehmers in der allgemeinen gesetzlichen
 * Rentenversicherung (4 Dezimalstellen)   */
double RVSATZAN = (double)0;
/*  Rechenwert in Gleitkommadarstellung  */
double RW = (double)0;
/*  Sonderausgaben-Pauschbetrag in EURO  */
double SAP = (double)0;
/*  Freigrenze fuer den Solidaritaetszuschlag in EURO  */
double SOLZFREI = (double)0;
/*  Solidaritaetszuschlag auf die Jahreslohnsteuer in EURO, C (2 Dezimalstellen)
 */
double SOLZJ = (double)0;
/*  Zwischenwert fuer den Solidaritaetszuschlag auf die Jahreslohnsteuer
                             in EURO, C (2 Dezimalstellen)  */
double SOLZMIN = (double)0;
/*  Neu ab 2021: Bemessungsgrundlage des Solidaritätszuschlags zur Prüfung der
 * Freigrenze beim Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für
 * mehrjährige Tätigkeit) in Euro  */
double SOLZSBMG = (double)0;
/*  Neu ab 2021: Zu versteuerndes Einkommen für die Ermittlung der
 * Bemessungsgrundlage des Solidaritätszuschlags zur Prüfung der Freigrenze beim
 * Solidaritätszuschlag für sonstige Bezüge (ohne Vergütung für mehrjährige
 * Tätigkeit) in Euro, Cent (2 Dezimalstellen)  */
double SOLZSZVE = (double)0;
/*  Neu ab 2021: Bemessungsgrundlage des Solidaritätszuschlags für die Prüfung
 * der Freigrenze beim Solidaritätszuschlag für die Vergütung für mehrjährige
 * Tätigkeit in Euro  */
double SOLZVBMG = (double)0;
/*  Tarifliche Einkommensteuer in EURO  */
double ST = (double)0;
/*  Tarifliche Einkommensteuer auf das 1,25-fache ZX in EURO  */
double ST1 = (double)0;
/*  Tarifliche Einkommensteuer auf das 0,75-fache ZX in EURO  */
double ST2 = (double)0;
/*  Zwischenfeld zur Ermittlung der Steuer auf Vergütungen für mehrjährige
 * Tätigkeit  */
double STOVMT = (double)0;
/*  Teilbetragssatz der Vorsorgepauschale für die Rentenversicherung (2
 * Dezimalstellen)  */
double TBSVORV = (double)0;
/*  Bemessungsgrundlage fuer den Versorgungsfreibetrag in Cents  */
double VBEZB = (double)0;
/*  Bemessungsgrundlage für den Versorgungsfreibetrag in Cent für
                             den sonstigen Bezug  */
double VBEZBSO = (double)0;
/*  Hoechstbetrag der Vorsorgepauschale nach Alterseinkuenftegesetz in EURO, C
 */
double VHB = (double)0;
/*  Vorsorgepauschale in EURO, C (2 Dezimalstellen)  */
double VSP = (double)0;
/*  Vorsorgepauschale nach Alterseinkuenftegesetz in EURO, C  */
double VSPN = (double)0;
/*  Zwischenwert 1 bei der Berechnung der Vorsorgepauschale nach
                             dem Alterseinkuenftegesetz in EURO, C (2
   Dezimalstellen)  */
double VSP1 = (double)0;
/*  Zwischenwert 2 bei der Berechnung der Vorsorgepauschale nach
                             dem Alterseinkuenftegesetz in EURO, C (2
   Dezimalstellen)  */
double VSP2 = (double)0;
/*  Vorsorgepauschale mit Teilbeträgen für die gesetzliche Kranken- und
                                         soziale Pflegeversicherung nach
   fiktiven Beträgen oder ggf. für die private Basiskrankenversicherung und
   private Pflege-Pflichtversicherung in Euro, Cent (2 Dezimalstellen)  */
double VSP3 = (double)0;
/*  Erster Grenzwert in Steuerklasse V/VI in Euro  */
double W1STKL5 = (double)0;
/*  Zweiter Grenzwert in Steuerklasse V/VI in Euro  */
double W2STKL5 = (double)0;
/*  Dritter Grenzwert in Steuerklasse V/VI in Euro  */
double W3STKL5 = (double)0;
/*  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2 Nr. 2 EStG in EURO  */
double VSPMAX1 = (double)0;
/*  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2 Nr. 3 EStG in EURO  */
double VSPMAX2 = (double)0;
/*  Vorsorgepauschale nach § 10c Abs. 2 Satz 2 EStG vor der
   Hoechstbetragsberechnung in EURO, C (2 Dezimalstellen)  */
double VSPO = (double)0;
/*  Fuer den Abzug nach § 10c Abs. 2 Nrn. 2 und 3 EStG verbleibender
                             Rest von VSPO in EURO, C (2 Dezimalstellen)  */
double VSPREST = (double)0;
/*  Hoechstbetrag der Vorsorgepauschale nach § 10c Abs. 2 Nr. 1 EStG
                             in EURO, C (2 Dezimalstellen)  */
double VSPVOR = (double)0;
/*  Zu versteuerndes Einkommen gem. § 32a Abs. 1 und 2 EStG €, C
                             (2 Dezimalstellen)  */
double X = (double)0;
/*  gem. § 32a Abs. 1 EStG (6 Dezimalstellen)  */
double Y = (double)0;
/*  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2 Dezimalstellen)
                             nach Abzug der Freibeträge nach § 39 b Abs. 2 Satz
   3 und 4.  */
double ZRE4 = (double)0;
/*  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2 Dezimalstellen)  */
double ZRE4J = (double)0;
/*  Auf einen Jahreslohn hochgerechnetes RE4 in €, C (2 Dezimalstellen)
                             nach Abzug des Versorgungsfreibetrags und des
   Alterentlastungsbetrags zur Berechnung der Vorsorgepauschale in €, Cent (2
   Dezimalstellen)  */
double ZRE4VP = (double)0;
/*  Feste Tabellenfreibeträge (ohne Vorsorgepauschale) in €, Cent
                             (2 Dezimalstellen)  */
double ZTABFB = (double)0;
/*  Auf einen Jahreslohn hochgerechnetes (VBEZ abzueglich FVB) in
                             EURO, C (2 Dezimalstellen)  */
double ZVBEZ = (double)0;
/*  Auf einen Jahreslohn hochgerechnetes VBEZ in €, C (2 Dezimalstellen)  */
double ZVBEZJ = (double)0;
/*  Zu versteuerndes Einkommen in €, C (2 Dezimalstellen)  */
double ZVE = (double)0;
/*  Zwischenfelder zu X fuer die Berechnung der Steuer nach § 39b
                             Abs. 2 Satz 7 EStG in €  */
double ZX = (double)0;
double ZZX = (double)0;
double HOCH = (double)0;
double VERGL = (double)0;
/*  Jahreswert der berücksichtigten Beiträge zur privaten
   Basis-Krankenversicherung und
                                          privaten Pflege-Pflichtversicherung
   (ggf. auch die Mindestvorsorgepauschale) in Cent.  */
double VKV = (double)0;

/*  Tabelle fuer die Vomhundertsaetze des Versorgungsfreibetrags  */
double[] TAB1 = {
    (double)0.0,   (double)0.4,  (double)0.384, (double)0.368, (double)0.352,
    (double)0.336, (double)0.32, (double)0.304, (double)0.288, (double)0.272,
    (double)0.256, (double)0.24, (double)0.224, (double)0.208, (double)0.192,
    (double)0.176, (double)0.16, (double)0.152, (double)0.144, (double)0.136,
    (double)0.128, (double)0.12, (double)0.112, (double)0.104, (double)0.096,
    (double)0.088, (double)0.08, (double)0.072, (double)0.064, (double)0.056,
    (double)0.048, (double)0.04, (double)0.032, (double)0.024, (double)0.016,
    (double)0.008, (double)0.0};
/*  Tabelle fuer die Hoechstbetrage des Versorgungsfreibetrags  */
double[] TAB2 = {
    (double)0,    (double)3000, (double)2880, (double)2760, (double)2640,
    (double)2520, (double)2400, (double)2280, (double)2160, (double)2040,
    (double)1920, (double)1800, (double)1680, (double)1560, (double)1440,
    (double)1320, (double)1200, (double)1140, (double)1080, (double)1020,
    (double)960,  (double)900,  (double)840,  (double)780,  (double)720,
    (double)660,  (double)600,  (double)540,  (double)480,  (double)420,
    (double)360,  (double)300,  (double)240,  (double)180,  (double)120,
    (double)60,   (double)0};
/*  Tabelle fuer die Zuschlaege zum Versorgungsfreibetrag  */
double[] TAB3 = {
    (double)0,   (double)900, (double)864, (double)828, (double)792,
    (double)756, (double)720, (double)684, (double)648, (double)612,
    (double)576, (double)540, (double)504, (double)468, (double)432,
    (double)396, (double)360, (double)342, (double)324, (double)306,
    (double)288, (double)270, (double)252, (double)234, (double)216,
    (double)198, (double)180, (double)162, (double)144, (double)126,
    (double)108, (double)90,  (double)72,  (double)54,  (double)36,
    (double)18,  (double)0};
/*  Tabelle fuer die Vomhundertsaetze des Altersentlastungsbetrags  */
double[] TAB4 = {
    (double)0.0,   (double)0.4,  (double)0.384, (double)0.368, (double)0.352,
    (double)0.336, (double)0.32, (double)0.304, (double)0.288, (double)0.272,
    (double)0.256, (double)0.24, (double)0.224, (double)0.208, (double)0.192,
    (double)0.176, (double)0.16, (double)0.152, (double)0.144, (double)0.136,
    (double)0.128, (double)0.12, (double)0.112, (double)0.104, (double)0.096,
    (double)0.088, (double)0.08, (double)0.072, (double)0.064, (double)0.056,
    (double)0.048, (double)0.04, (double)0.032, (double)0.024, (double)0.016,
    (double)0.008, (double)0.0};
/*  Tabelle fuer die Hoechstbetraege des Altersentlastungsbetrags  */
double[] TAB5 = {
    (double)0,    (double)1900, (double)1824, (double)1748, (double)1672,
    (double)1596, (double)1520, (double)1444, (double)1368, (double)1292,
    (double)1216, (double)1140, (double)1064, (double)988,  (double)912,
    (double)836,  (double)760,  (double)722,  (double)684,  (double)646,
    (double)608,  (double)570,  (double)532,  (double)494,  (double)456,
    (double)418,  (double)380,  (double)342,  (double)304,  (double)266,
    (double)228,  (double)190,  (double)152,  (double)114,  (double)76,
    (double)38,   (double)0};
/*  Zahlenkonstanten fuer im Plan oft genutzte double Werte  */
double ZAHL1 = 1.0;
double ZAHL2 = (double)2;
double ZAHL5 = (double)5;
double ZAHL7 = (double)7;
double ZAHL12 = (double)12;
double ZAHL100 = (double)100;
double ZAHL360 = (double)360;
double ZAHL500 = (double)500;
double ZAHL700 = (double)700;
double ZAHL1000 = (double)1000;
double ZAHL10000 = (double)10000;

/*  PROGRAMMABLAUFPLAN, PAP Seite 14  */
int main() {
  //%INPUT%
  MPARA();
  MRE4JL();
  VBEZBSO = 0.0;
  KENNVMT = 0;
  MRE4();
  MRE4ABZ();
  MBERECH();
  MSONST();
  MVMT();
  //%OUTPUT%
  return 0;
}
/*  Zuweisung von Werten für bestimmte Sozialversicherungsparameter  PAP Seite
 * 15  */
void MPARA() {
  if (KRV < 2)
  /*  &lt; = <  */
  {
    if (KRV == 0) {
      BBGRV = 84600;
      /*  Geändert für 2022  */
    } else {
      BBGRV = 81000;
      /*  Geändert für 2022  */
    }

    RVSATZAN = 0.093;
    /*  Neu 2019  */
    TBSVORV = 0.88;
    /*  Geändert für 2022 */
  } else {
    /*  Nichts zu tun  */
  }

  BBGKVPV = 58050;
  /*  Geändert für 2021  */
  bd = 2;
  /*  Neu 2019  */
  KVSATZAN = (((KVZ / bd) / ZAHL100) + 0.07);
  /*  Neu 2019  */
  KVSATZAG = 0.0065 + 0.07;
  /*  Geändert für 2021 */
  if (PVS == 1) {
    PVSATZAN = 0.02025;
    /*  Neu 2019  */
    PVSATZAG = 0.01025;
    /*  Neu 2019  */
  } else {
    PVSATZAN = 0.01525;
    /*  Neu 2019  */
    PVSATZAG = 0.01525;
    /*  Neu 2019  */
  }

  if (PVZ == 1) {
    PVSATZAN = (PVSATZAN + 0.0035);
    /*   geändert für 2022  */
  }

  /*  Anfang Geändert für 2022  */
  W1STKL5 = 11480;
  W2STKL5 = 29298;
  W3STKL5 = 222260;
  GFB = 9984;
  /*  Ende Geändert für 2022  */
  /*  Anfang Geändert für 2021  */
  SOLZFREI = 16956;
  /*  Ende Geändert für 2021  */
}
/*  Ermittlung des Jahresarbeitslohns nach § 39 b Abs. 2 Satz 2 EStG, PAP Seite
 * 16  */
void MRE4JL() {
  if (LZZ == 1) {
    ZRE4J = round_down(RE4 / ZAHL100, 2);
    ZVBEZJ = round_down(VBEZ / ZAHL100, 2);
    JLFREIB = round_down(LZZFREIB / ZAHL100, 2);
    JLHINZU = round_down(LZZHINZU / ZAHL100, 2);
  } else {
    if (LZZ == 2) {
      ZRE4J = round_down((RE4 * ZAHL12) / ZAHL100, 2);
      ZVBEZJ = round_down((VBEZ * ZAHL12) / ZAHL100, 2);
      JLFREIB = round_down((LZZFREIB * ZAHL12) / ZAHL100, 2);
      JLHINZU = round_down((LZZHINZU * ZAHL12) / ZAHL100, 2);
    } else {
      if (LZZ == 3) {
        ZRE4J = round_down((RE4 * ZAHL360) / ZAHL700, 2);
        ZVBEZJ = round_down((VBEZ * ZAHL360) / ZAHL700, 2);
        JLFREIB = round_down((LZZFREIB * ZAHL360) / ZAHL700, 2);
        JLHINZU = round_down((LZZHINZU * ZAHL360) / ZAHL700, 2);
      } else {
        ZRE4J = round_down((RE4 * ZAHL360) / ZAHL100, 2);
        ZVBEZJ = round_down((VBEZ * ZAHL360) / ZAHL100, 2);
        JLFREIB = round_down((LZZFREIB * ZAHL360) / ZAHL100, 2);
        JLHINZU = round_down((LZZHINZU * ZAHL360) / ZAHL100, 2);
      }
    }
  }

  if (af == 0) {
    f = 1;
  }
}
/*  Freibeträge für Versorgungsbezüge, Altersentlastungsbetrag (§ 39b Abs. 2
 * Satz 3 EStG), PAP Seite 17  */
void MRE4() {
  if ((ZVBEZJ == 0.0)) {
    FVBZ = 0.0;
    FVB = 0.0;
    FVBZSO = 0.0;
    FVBSO = 0.0;
  } else {
    if (VJAHR < 2006) {
      J = 1;
    } else {
      if (VJAHR < 2040) {
        J = VJAHR - 2004;
      } else {
        J = 36;
      }
    }

    if (LZZ == 1) {
      VBEZB = ((VBEZM * ZMVB) + VBEZS);
      HFVB = TAB2[J];
      FVBZ = TAB3[J];
    } else {
      VBEZB = round_down(((VBEZM * ZAHL12) + VBEZS), 2);
      HFVB = TAB2[J];
      FVBZ = TAB3[J];
    }

    FVB = round_up(((VBEZB * TAB1[J]) / ZAHL100), 2);
    if ((FVB > HFVB)) {
      FVB = HFVB;
    }

    if ((FVB > ZVBEZJ)) {
      FVB = ZVBEZJ;
    }

    FVBSO = round_up((FVB + ((VBEZBSO * TAB1[J]) / ZAHL100)), 2);
    if ((FVBSO > TAB2[J])) {
      FVBSO = TAB2[J];
    }

    HFVBZSO = round_down((((VBEZB + VBEZBSO) / ZAHL100) - FVBSO), 2);
    FVBZSO = round_up((FVBZ + (VBEZBSO / ZAHL100)), 0);
    if ((FVBZSO > HFVBZSO)) {
      FVBZSO = round_up(HFVBZSO, 0);
    }

    if ((FVBZSO > TAB3[J])) {
      FVBZSO = TAB3[J];
    }

    HFVBZ = round_down(((VBEZB / ZAHL100) - FVB), 2);
    if ((FVBZ > HFVBZ)) {
      FVBZ = round_up(HFVBZ, 0);
    }
  }

  MRE4ALTE();
}
/*  Altersentlastungsbetrag (§ 39b Abs. 2 Satz 3 EStG), PAP Seite 18  */
void MRE4ALTE() {
  if (ALTER1 == 0) {
    ALTE = 0.0;
  } else {
    if (AJAHR < 2006) {
      K = 1;
    } else {
      if (AJAHR < 2040) {
        K = AJAHR - 2004;
      } else {
        K = 36;
      }
    }

    BMG = (ZRE4J - ZVBEZJ);
    /*  Lt. PAP muss hier auf ganze EUR gerundet werden  */
    ALTE = round_up((BMG * TAB4[K]), 0);
    HBALTE = TAB5[K];
    if ((ALTE > HBALTE)) {
      ALTE = HBALTE;
    }
  }
}
/*  Ermittlung des Jahresarbeitslohns nach Abzug der Freibeträge nach § 39 b
 * Abs. 2 Satz 3 und 4 EStG, PAP Seite 20  */
void MRE4ABZ() {
  ZRE4 = round_down(((((ZRE4J - FVB) - ALTE) - JLFREIB) + JLHINZU), 2);
  if ((ZRE4 < 0.0)) {
    ZRE4 = 0.0;
  }

  ZRE4VP = ZRE4J;
  if (KENNVMT == 2) {
    ZRE4VP = round_down((ZRE4VP - (ENTSCH / ZAHL100)), 2);
  }

  ZVBEZ = round_down((ZVBEZJ - FVB), 2);
  if ((ZVBEZ < 0.0)) {
    ZVBEZ = 0.0;
  }
}
/*  Berechnung fuer laufende Lohnzahlungszeitraueme Seite 21 */
void MBERECH() {
  MZTABFB();
  VFRB = round_down(((ANP + (FVB + FVBZ)) * ZAHL100), 0);
  MLSTJAHR();
  WVFRB = round_down(((ZVE - GFB) * ZAHL100), 0);
  if ((WVFRB < 0.0))
  /*  WVFRB < 0  */
  {
    WVFRB = 0;
  }

  LSTJAHR = round_down((ST * f), 0);
  UPLSTLZZ();
  UPVKVLZZ();
  if ((ZKF > 0.0))
  /*  ZKF > 0  */
  {
    ZTABFB = (ZTABFB + KFB);
    MRE4ABZ();
    MLSTJAHR();
    JBMG = round_down((ST * f), 0);
  } else {
    JBMG = LSTJAHR;
  }

  MSOLZ();
}
/*  Ermittlung der festen Tabellenfreibeträge (ohne Vorsorgepauschale), PAP
 * Seite 22  */
void MZTABFB() {
  ANP = 0.0;
  if ((ZVBEZ >= 0.0) && (ZVBEZ < FVBZ)) {
    FVBZ = round_down(ZVBEZ, 0);
  }

  if (STKL < 6) {
    if ((ZVBEZ > 0.0)) {
      if (((ZVBEZ - FVBZ) < 102)) {
        ANP = round_up((ZVBEZ - FVBZ), 0);
      } else {
        ANP = 102;
      }
    }

  } else {
    FVBZ = 0;
    FVBZSO = 0;
  }

  if (STKL < 6) {
    if ((ZRE4 > ZVBEZ)) {
      if (((ZRE4 - ZVBEZ) < ZAHL1000)) {
        ANP = round_up(((ANP + ZRE4) - ZVBEZ), 0);
      } else {
        ANP = (ANP + ZAHL1000);
      }
    }
  }

  KZTAB = 1;
  if (STKL == 1) {
    SAP = 36;
    KFB = round_down((ZKF * 8388), 0);
    /*  Geändert für 2021  */
  } else {
    if (STKL == 2) {
      EFA = 4008;
      /*  mod f 2022  */
      SAP = 36;
      KFB = round_down((ZKF * 8388), 0);
      /*  Geändert für 2021  */
    } else {
      if (STKL == 3) {
        KZTAB = 2;
        SAP = 36;
        KFB = round_down((ZKF * 8388), 0);
        /*  Geändert für 2021  */
      } else {
        if (STKL == 4) {
          SAP = 36;
          KFB = round_down((ZKF * 4194), 0);
          /*  Geändert für 2021  */
        } else {
          if (STKL == 5) {
            SAP = 36;
            KFB = 0.0;
          } else {
            KFB = 0.0;
          }
        }
      }
    }
  }

  ZTABFB = round_down((((EFA + ANP) + SAP) + FVBZ), 2);
}
/*  Ermittlung Jahreslohnsteuer, PAP Seite 23  */
void MLSTJAHR() {
  UPEVP();
  if (KENNVMT != 1) {
    ZVE = round_down(((ZRE4 - ZTABFB) - VSP), 2);
    UPMLST();
  } else {
    ZVE = round_down(
        ((((ZRE4 - ZTABFB) - VSP) - (VMT / ZAHL100)) - (VKAPA / ZAHL100)), 2);
    if ((ZVE < 0.0)) {
      ZVE = round_down((((ZVE + (VMT / ZAHL100)) + (VKAPA / ZAHL100)) / ZAHL5),
                       2);
      UPMLST();
      ST = round_down((ST * ZAHL5), 0);
    } else {
      UPMLST();
      STOVMT = ST;
      ZVE = round_down((ZVE + ((VMT + VKAPA) / ZAHL500)), 2);
      UPMLST();
      ST = round_down((((ST - STOVMT) * ZAHL5) + STOVMT), 0);
    }
  }
}
/*  PAP Seite 24  */
void UPVKVLZZ() {
  UPVKV();
  JW = VKV;
  UPANTEIL();
  VKVLZZ = ANTEIL1;
}
/*  PAP Seite 24  */
void UPVKV() {
  if (PKV > 0) {
    if ((VSP2 > VSP3)) {
      VKV = (VSP2 * ZAHL100);
    } else {
      VKV = (VSP3 * ZAHL100);
    }

  } else {
    VKV = 0.0;
  }
}
/*  PAP Seite 25  */
void UPLSTLZZ() {
  JW = (LSTJAHR * ZAHL100);
  UPANTEIL();
  LSTLZZ = ANTEIL1;
}
/*  Ermittlung der Jahreslohnsteuer aus dem Einkommensteuertarif. PAP Seite 26
 */
void UPMLST() {
  if ((ZVE < ZAHL1)) {
    ZVE = 0.0;
    X = 0.0;
  } else {
    X = round_down((ZVE / KZTAB), 0);
  }

  if (STKL < 5) {
    /*  Änderung für 2022  */
    UPTAB22();
  } else {
    MST5_6();
  }
}
/*  	Vorsorgepauschale (§ 39b Absatz 2 Satz 5 Nummer 3 und Absatz 4 EStG)
 * PAP Seite 27   */
void UPEVP() {
  if (KRV > 1)
  /*  &lt; = < &gt; = >  */
  {
    VSP1 = 0.0;
  } else {
    if ((ZRE4VP > BBGRV)) {
      ZRE4VP = BBGRV;
    }

    VSP1 = round_down((TBSVORV * ZRE4VP), 2);
    VSP1 = round_down((VSP1 * RVSATZAN), 2);
  }

  VSP2 = round_down((ZRE4VP * 0.12), 2);
  if (STKL == 3) {
    VHB = 3000;
  } else {
    VHB = 1900;
  }

  if ((VSP2 > VHB)) {
    VSP2 = VHB;
  }

  VSPN = round_up((VSP1 + VSP2), 0);
  MVSP();
  if ((VSPN > VSP)) {
    VSP = round_down(VSPN, 2);
  }
}
/*  Vorsorgepauschale (§39b Abs. 2 Satz 5 Nr 3 EStG) Vergleichsberechnung fuer
 * Guenstigerpruefung, PAP Seite 28  */
void MVSP() {
  if ((ZRE4VP > BBGKVPV)) {
    ZRE4VP = BBGKVPV;
  }

  if (PKV > 0) {
    if (STKL == 6) {
      VSP3 = 0.0;
    } else {
      VSP3 = ((PKPV * ZAHL12) / ZAHL100);
      if (PKV == 2) {
        VSP3 = round_down((VSP3 - (ZRE4VP * (KVSATZAG + PVSATZAG))), 2);
      }
    }

  } else {
    VSP3 = round_down((ZRE4VP * (KVSATZAN + PVSATZAN)), 2);
  }

  VSP = round_up((VSP3 + VSP1), 0);
}
/*  Lohnsteuer fuer die Steuerklassen V und VI (§ 39b Abs. 2 Satz 7 EStG), PAP
 * Seite 29  */
void MST5_6() {
  ZZX = X;
  if ((ZZX > W2STKL5)) {
    ZX = W2STKL5;
    UP5_6();
    if ((ZZX > W3STKL5)) {
      ST = round_down((ST + ((W3STKL5 - W2STKL5) * 0.42)), 0);
      ST = round_down((ST + ((ZZX - W3STKL5) * 0.45)), 0);
    } else {
      ST = round_down((ST + ((ZZX - W2STKL5) * 0.42)), 0);
    }

  } else {
    ZX = ZZX;
    UP5_6();
    if ((ZZX > W1STKL5)) {
      VERGL = ST;
      ZX = W1STKL5;
      UP5_6();
      HOCH = round_down((ST + ((ZZX - W1STKL5) * 0.42)), 0);
      /*  Neuer Wert 2014  */
      if ((HOCH < VERGL)) {
        ST = HOCH;
      } else {
        ST = VERGL;
      }
    }
  }
}
/*  Unterprogramm zur Lohnsteuer fuer die Steuerklassen V und VI (§ 39b Abs. 2
 * Satz 7 EStG), PAP Seite 30  */
void UP5_6() {
  X = round_down((ZX * 1.25), 2);
  /*  Änderung für 2022  */
  UPTAB22();
  ST1 = ST;
  X = round_down((ZX * 0.75), 2);
  /*  Änderung für 2022  */
  UPTAB22();
  ST2 = ST;
  DIFF = ((ST1 - ST2) * ZAHL2);
  MIST = round_down((ZX * 0.14), 0);
  if ((MIST > DIFF)) {
    ST = MIST;
  } else {
    ST = DIFF;
  }
}
/*  Solidaritaetszuschlag, PAP Seite 31  */
void MSOLZ() {
  SOLZFREI = (SOLZFREI * KZTAB);
  if ((JBMG > SOLZFREI)) {
    SOLZJ = round_down(((JBMG * 5.5) / ZAHL100), 2);
    SOLZMIN = round_down((((JBMG - SOLZFREI) * 11.9) / ZAHL100), 2);
    /*  Änderung für 2021  */
    if ((SOLZMIN < SOLZJ)) {
      SOLZJ = SOLZMIN;
    }

    JW = round_down((SOLZJ * ZAHL100), 0);
    UPANTEIL();
    SOLZLZZ = ANTEIL1;
  } else {
    SOLZLZZ = 0.0;
  }

  if (R > 0) {
    JW = (JBMG * ZAHL100);
    UPANTEIL();
    BK = ANTEIL1;
  } else {
    BK = 0.0;
  }
}
/*  Anteil von Jahresbetraegen fuer einen LZZ (§ 39b Abs. 2 Satz 9 EStG), PAP
 * Seite 32  */
void UPANTEIL() {
  if (LZZ == 1) {
    ANTEIL1 = JW;
  } else {
    if (LZZ == 2) {
      ANTEIL1 = round_down(JW / ZAHL12, 0);
    } else {
      if (LZZ == 3) {
        ANTEIL1 = round_down((JW * ZAHL7) / ZAHL360, 0);
      } else {
        ANTEIL1 = round_down(JW / ZAHL360, 0);
      }
    }
  }
}
/*  Berechnung sonstiger Bezuege nach § 39b Abs. 3 Saetze 1 bis 8 EStG), PAP
 * Seite 33  */
void MSONST() {
  LZZ = 1;
  if (ZMVB == 0) {
    ZMVB = 12;
  }

  if ((SONSTB == 0.0) && (MBV == 0.0))
  /*  neu für 2022  */
  {
    VKVSONST = 0.0;
    LSTSO = 0.0;
    STS = 0.0;
    SOLZS = 0.0;
    BKS = 0.0;
  } else {
    MOSONST();
    UPVKV();
    VKVSONST = VKV;
    ZRE4J = round_down(((JRE4 + SONSTB) / ZAHL100), 2);
    ZVBEZJ = round_down(((JVBEZ + VBS) / ZAHL100), 2);
    VBEZBSO = STERBE;
    MRE4SONST();
    MLSTJAHR();
    WVFRBM = round_down(((ZVE - GFB) * ZAHL100), 2);
    if ((WVFRBM < 0.0))
    /*  WVFRBM < 0  */
    {
      WVFRBM = 0.0;
    }

    UPVKV();
    VKVSONST = (VKV - VKVSONST);
    LSTSO = (ST * ZAHL100);
    /*  lt. PAP:  "Hinweis: negative Zahlen werden nach ihrem Betrag gerundet!"
     */
    /*  Fallunterscheidung bzgl. negativer Zahlen nicht nötig, da die
     * Java-Klasse double.ROUND_DOWN   */
    /*  die Ziffer und nicht die Zahl abrundet, also aus -4.5 wird -4 und
     * aus 4.5 wird 4  */
    STS = (round_down(((LSTSO - LSTOSO) * f) / ZAHL100, 0) * ZAHL100);
    /*  Neu für 2022  */
    STSMIN();
  }
}
/*  Neu für 2022  */
void STSMIN() {
  if ((STS < 0.0))
  /*  STS < 0  */
  {
    if ((MBV == 0.0))
    /*   MBV = 0   */
    {
      /*  absichtlich leer  */
    } else {
      LSTLZZ = (LSTLZZ + STS);
      if ((LSTLZZ < 0.0))
      /*   LSTLZZ < 0  */
      {
        LSTLZZ = 0.0;
      }

      SOLZLZZ = round_down((SOLZLZZ + (STS * (5.5 / ZAHL100))), 0);
      if ((SOLZLZZ < 0.0))
      /*   SOLZLZZ < 0  */
      {
        SOLZLZZ = 0.0;
      }

      BK = (BK + STS);
      if ((BK < 0.0))
      /*   BK < 0  */
      {
        BK = 0.0;
      }
    }

    STS = 0.0;
    SOLZS = 0.0;
  } else {
    MSOLZSTS();
  }

  if (R > 0) {
    BKS = STS;
  } else {
    BKS = 0.0;
  }
}
/*  Berechnung des SolZ auf sonstige Bezüge, PAP Seite 34, Neu ab 2021  */
void MSOLZSTS() {
  if ((ZKF > 0.0))
  /*  ZKF > 0  */
  {
    SOLZSZVE = (ZVE - KFB);
  } else {
    SOLZSZVE = ZVE;
  }

  if ((SOLZSZVE < 0.0))
  /*  SOLZSZVE < 1  */
  {
    SOLZSZVE = 0.0;
    X = 0.0;
  } else {
    X = round_down(SOLZSZVE / KZTAB, 0);
  }

  if (STKL < 5)
  /*  STKL < 5  */
  {
    /*  Änderung für 2022  */
    UPTAB22();
  } else {
    MST5_6();
  }

  SOLZSBMG = round_down((ST * f), 0);
  if ((SOLZSBMG > SOLZFREI))
  /*  SOLZSBMG > SOLZFREI  */
  {
    SOLZS = round_down((STS * 5.5) / ZAHL100, 0);
  } else {
    SOLZS = 0.0;
  }
}
/*  Berechnung der Verguetung fuer mehrjaehrige Taetigkeit nach § 39b Abs. 3
 * Satz 9 und 10 EStG), PAP Seite 35  */
void MVMT() {
  if ((VKAPA < 0.0)) {
    VKAPA = 0.0;
  }

  if (((VMT + VKAPA) > 0.0)) {
    if ((LSTSO == 0.0)) {
      MOSONST();
      LST1 = LSTOSO;
    } else {
      LST1 = LSTSO;
    }

    VBEZBSO = (STERBE + VKAPA);
    ZRE4J = round_down(((((JRE4 + SONSTB) + VMT) + VKAPA) / ZAHL100), 2);
    ZVBEZJ = round_down((((JVBEZ + VBS) + VKAPA) / ZAHL100), 2);
    KENNVMT = 2;
    MRE4SONST();
    MLSTJAHR();
    LST3 = (ST * ZAHL100);
    MRE4ABZ();
    ZRE4VP = ((ZRE4VP - (JRE4ENT / ZAHL100)) - (SONSTENT / ZAHL100));
    KENNVMT = 1;
    MLSTJAHR();
    LST2 = (ST * ZAHL100);
    STV = (LST2 - LST1);
    LST3 = (LST3 - LST1);
    if ((LST3 < STV)) {
      STV = LST3;
    }

    if ((STV < 0.0)) {
      STV = 0.0;
    } else {
      /*
                                      lt. PAP muss hier auf ganze EUR abgerundet
         werden. Allerdings muss auch hier der Wert in Cent vorgehalten werden,
                                      weshalb nach dem Aufrunden auf ganze EUR
         durch 'divide(ZAHL100, 0, double.ROUND_DOWN)' wieder die Multiplikation
         mit 100 erfolgt.
                               */
      STV = (round_down((STV * f) / ZAHL100, 0) * ZAHL100);
    }

    /*  Beginn Neu 2021  */
    SOLZVBMG = (round_down(STV / ZAHL100, 0) + JBMG);
    if ((SOLZVBMG > SOLZFREI))
    /*  SOLZVBMG > SOLZFREI  */
    {
      SOLZV = round_down((STV * 5.5) / ZAHL100, 0);
    } else {
      SOLZV = 0.0;
    }

    /*  Ende Neu 2021  */
    if (R > 0) {
      BKV = STV;
    } else {
      BKV = 0.0;
    }

  } else {
    STV = 0.0;
    SOLZV = 0.0;
    BKV = 0.0;
  }
}
/*  Sonderberechnung ohne sonstige Bezüge für Berechnung bei sonstigen Bezügen
 * oder Vergütung für mehrjährige Tätigkeit, PAP Seite 36  */
void MOSONST() {
  ZRE4J = round_down((JRE4 / ZAHL100), 2);
  ZVBEZJ = round_down((JVBEZ / ZAHL100), 2);
  JLFREIB = round_down(JFREIB / ZAHL100, 2);
  JLHINZU = round_down(JHINZU / ZAHL100, 2);
  MRE4();
  MRE4ABZ();
  ZRE4VP = (ZRE4VP - (JRE4ENT / ZAHL100));
  MZTABFB();
  VFRBS1 = round_down(((ANP + (FVB + FVBZ)) * ZAHL100), 2);
  MLSTJAHR();
  WVFRBO = round_down(((ZVE - GFB) * ZAHL100), 2);
  if ((WVFRBO < 0.0)) {
    WVFRBO = 0.0;
  }

  LSTOSO = (ST * ZAHL100);
}
/*  Sonderberechnung mit sonstige Bezüge für Berechnung bei sonstigen Bezügen
 * oder Vergütung für mehrjährige Tätigkeit, PAP Seite 37  */
void MRE4SONST() {
  MRE4();
  FVB = FVBSO;
  MRE4ABZ();
  /*  Änderung für 2022   */
  ZRE4VP = (((ZRE4VP + (MBV / ZAHL100)) - (JRE4ENT / ZAHL100)) -
            (SONSTENT / ZAHL100));
  FVBZ = FVBZSO;
  MZTABFB();
  VFRBS2 = ((((ANP + FVB) + FVBZ) * ZAHL100) - VFRBS1);
}
/*  Komplett Neu 2020  */
/*  Tarifliche Einkommensteuer §32a EStG, PAP Seite 38  */
void UPTAB22() {
  /*  Änderung für 2022  */
  if ((X < (GFB + ZAHL1))) {
    ST = 0.0;
  } else {
    if ((X < 14927))
    /*  Geändert für 2022  */
    {
      Y = round_down((X - GFB) / ZAHL10000, 6);
      RW = (Y * 1008.7);
      /*  Geändert für 2022  */
      RW = (RW + 1400);
      ST = round_down((RW * Y), 0);
    } else {
      if ((X < 58597))
      /*  Geändert für 2022  */
      {
        Y = round_down((X - 14926) / ZAHL10000, 6);
        /*  Geändert für 2022   */
        RW = (Y * 206.43);
        /*  Geändert für 2022  */
        RW = (RW + 2397);
        RW = (RW * Y);
        ST = round_down((RW + 938.24), 0);
        /*  Geändert für 2022  */
      } else {
        if ((X < 277826))
        /*  Geändert für 2022  */
        {
          ST = round_down(((X * 0.42) - 9267.53), 0);
          /*  Geändert für 2022  */
        } else {
          ST = round_down(((X * 0.45) - 17602.28), 0);
          /*  Geändert für 2022  */
        }
      }
    }
  }

  ST = (ST * KZTAB);
}
