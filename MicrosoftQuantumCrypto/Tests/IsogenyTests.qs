// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.Crypto.Tests.Isogenies {
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Diagnostics;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;

    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.Fp2Arithmetic;
    open Microsoft.Quantum.Crypto.Isogenies;

    // To test various SIKE operations, we need to have 
    // very specially formed primes and points.

    /// # Summary
    /// Parameters for elliptic curves that resemble
    /// the SIKE protocol.
    ///
    /// # Elements
    /// ## prime
    /// A prime of the form $2^e3^f+c$, where c is
    /// small. 
    /// ## twoOrder
    /// The exponent e in the prime
    /// ## pointP
    /// A point P on the curve $y^2 = x^3 + 6x^2 + x$
    /// over $F_{p^2}$ with exact order $2^e$. This must
    /// have the property that $[2^{e-1}]P = (0:0:1)$.
    /// ## pointQ
    /// A point Q on the same curve with exact order $2^e$.
    /// This must have the property that 
    /// $[2^{e-1}]Q \neq (0:0:1)$.
    /// ## pointR
    /// The point equal to Q - P (equivalently, P - Q,
    /// since the projective (X:Z) coordinates do not include
    /// sign). Because of the requirements of P and Q, 
    /// this also has exact order $2^e$.
    newtype SIKEParams = (
        prime : BigInt, 
        twoOrder : Int, 
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointR : ECPointMontgomeryXZClassical
    );

    /// # Summary
    /// Returns SIKE-like parameters with the maximum available
    /// two-torsion that is at most as large as an input parameter.
    ///
    /// # Inputs
    /// ## twoTorsion
    /// The maximum two-torsion of the curve (i.e., the points
    /// P, Q, and R will all have order at most equal to this
    /// value).
    ///
    /// # Output
    /// ## SIKEParams
    /// A set of parameters for a SIKE-like elliptic curve.
    /// 
    /// # Remarks
    /// This function has many values for the parameters
    /// hard-coded in, output from SAGE. Most are not "proper"
    /// SIKE parameters: they do not balance the three-torsion
    /// and two-torsion subgroups. 
    ///
    /// If e is the returned two-Torsion, the number of bits
    /// of the prime returned is between e and 3e + 1.
    function GetSIKEParams(twoTorsion : Int) : SIKEParams {
        mutable prime = 0L;
        mutable pXReal = 0L;
        mutable pXImag = 0L;
        mutable pZReal = 0L;
        mutable pZImag = 0L;
        mutable qXReal = 0L;
        mutable qXImag = 0L;
        mutable qZReal = 0L;
        mutable qZImag = 0L;
        mutable rXReal = 0L;
        mutable rXImag = 0L;
        mutable rZReal = 0L;
        mutable rZImag = 0L;
        mutable twoIndex = 0;
        Fact(twoTorsion >= 4, $"Two torsion of {twoTorsion} is too small for SIKE");
        if (twoTorsion < 5){
            set prime = 431L;
            set qXReal = 429L;
            set qXImag = 398L;
            set pXReal = 386L;
            set pXImag = 173L;
            set rXReal = 214L;
            set rXImag = 178L;
            set twoIndex = 4;
        } elif (twoTorsion < 8){
            set prime = 863L;
            set qXReal = 95L;
            set qXImag = 448L;
            set pXReal = 196L;
            set pXImag = 713L;
            set rXReal = 609L;
            set rXImag = 121L;
            set twoIndex = 5;
        } elif (twoTorsion <10){	
            set prime = 6911L;	set twoIndex = 8;
            set qXReal = 5832L;	    set qXImag = 1244L;
            set pXReal = 6344L;	    set pXImag = 4128L;
            set rXReal = 5321L;	    set rXImag = 6181L;
        }	
        elif (twoTorsion <11){	
            set prime = 27647L;	set twoIndex = 10;
            set qXReal = 24212L;	    set qXImag = 21451L;
            set pXReal = 25243L;	    set pXImag = 16524L;
            set rXReal = 20687L;	    set rXImag = 18576L;
        }	
        elif (twoTorsion <12){	
            set prime = 6143L;	set twoIndex = 11;
            set qXReal = 3965L;	    set qXImag = 4999L;
            set pXReal = 5677L;	    set pXImag = 5311L;
            set rXReal = 2121L;	    set rXImag = 1139L;
        }	
        elif (twoTorsion <13){	
            set prime = 995327L;	set twoIndex = 12;
            set qXReal = 703689L;	    set qXImag = 969428L;
            set pXReal = 537555L;	    set pXImag = 27591L;
            set rXReal = 354639L;	    set rXImag = 548013L;
        }	
        elif (twoTorsion <14){	
            set prime = 8191L;	set twoIndex = 13;
            set qXReal = 1312L;	    set qXImag = 7848L;
            set pXReal = 1036L;	    set pXImag = 850L;
            set rXReal = 6101L;	    set rXImag = 7172L;
        }	
        elif (twoTorsion <15){	
            set prime = 442367L;	set twoIndex = 14;
            set qXReal = 223052L;	    set qXImag = 294289L;
            set pXReal = 234059L;	    set pXImag = 410023L;
            set rXReal = 252582L;	    set rXImag = 381961L;
        }	
        elif (twoTorsion <17){	
            set prime = 294911L;	set twoIndex = 15;
            set qXReal = 198657L;	    set qXImag = 60643L;
            set pXReal = 21725L;	    set pXImag = 50787L;
            set rXReal = 224483L;	    set rXImag = 208526L;
        }	
        elif (twoTorsion <18){	
            set prime = 131071L;	set twoIndex = 17;
            set qXReal = 17649L;	    set qXImag = 94690L;
            set pXReal = 85646L;	    set pXImag = 90073L;
            set rXReal = 129323L;	    set rXImag = 88309L;
        }	
        elif (twoTorsion <19){	
            set prime = 786431L;	set twoIndex = 18;
            set qXReal = 697688L;	    set qXImag = 522676L;
            set pXReal = 715860L;	    set pXImag = 360067L;
            set rXReal = 386551L;	    set rXImag = 510454L;
        }	
        elif (twoTorsion < 20){	
            set prime = 524287L;	set twoIndex = 19;
            set qXReal = 409293L;	    set qXImag = 400109L;
            set pXReal = 112270L;	    set pXImag = 493698L;
            set rXReal = 511449L;	    set rXImag = 54303L;
        }
        elif (twoTorsion <21){	
            set prime = 185752092671L;	set twoIndex = 20;
            set qXReal = 143697159255L;	    set qXImag = 48908565603L;
            set pXReal = 14649023691L;	    set pXImag = 130765838739L;
            set rXReal = 67530801242L;	    set rXImag = 1519577510L;
        }	
        elif (twoTorsion <22){	
            set prime = 18874367L;	set twoIndex = 21;
            set qXReal = 12616324L;	    set qXImag = 4733372L;
            set pXReal = 5527321L;	    set pXImag = 13620681L;
            set rXReal = 14194445L;	    set rXImag = 2416761L;
        }	
        elif (twoTorsion <23){	
            set prime = 9172942847L;	set twoIndex = 22;
            set qXReal = 4635685305L;	    set qXImag = 8675731273L;
            set pXReal = 1746876043L;	    set pXImag = 4567586887L;
            set rXReal = 7266291393L;	    set rXImag = 9097648461L;
        }	
        elif (twoTorsion <24){	
            set prime = 6115295231L;	set twoIndex = 23;
            set qXReal = 4544195908L;	    set qXImag = 3596863045L;
            set pXReal = 2173033879L;	    set pXImag = 5018940504L;
            set rXReal = 3040724935L;	    set rXImag = 3416187833L;
        }	
        elif (twoTorsion <27){	
            set prime = 4076863487L;	set twoIndex = 24;
            set qXReal = 1570219299L;	    set qXImag = 202425487L;
            set pXReal = 306157668L;	    set pXImag = 1905195556L;
            set rXReal = 37710261L;	    set rXImag = 2511148497L;
        }	
        elif (twoTorsion <28){	
            set prime = 10871635967L;	set twoIndex = 27;
            set qXReal = 1158935186L;	    set qXImag = 2744197520L;
            set pXReal = 138930515L;	    set pXImag = 9847781349L;
            set rXReal = 2717726850L;	    set rXImag = 1002941816L;
        }	
        elif (twoTorsion <29){	
            set prime = 7247757311L;	set twoIndex = 28;
            set qXReal = 4116165319L;	    set qXImag = 6271784856L;
            set pXReal = 499252743L;	    set pXImag = 6872818617L;
            set rXReal = 5559754204L;	    set rXImag = 6286920588L;
        }	
        elif (twoTorsion <30){	
            set prime = 1174136684543L;	set twoIndex = 29;
            set qXReal = 917812970882L;	    set qXImag = 84215873299L;
            set pXReal = 722011417884L;	    set pXImag = 1134521757789L;
            set rXReal = 1117140421045L;	    set rXImag = 548648812557L;
        }	
        elif (twoTorsion <31){	
            set prime = 2348273369087L;	set twoIndex = 30;
            set qXReal = 1892967968266L;	    set qXImag = 350961866889L;
            set pXReal = 438450595603L;	    set pXImag = 618418691498L;
            set rXReal = 779878038614L;	    set rXImag = 1132081423069L;
        }	
        elif (twoTorsion <32){	
            set prime = 2147483647L;	set twoIndex = 31;
            set qXReal = 793916560L;	    set qXImag = 1385107259L;
            set pXReal = 796985958L;	    set pXImag = 2063068448L;
            set rXReal = 640837647L;	    set rXImag = 109689585L;
        }	
        elif (twoTorsion <33){	
            set prime = 84537841287167L;	set twoIndex = 32;
            set qXReal = 18458686564419L;	    set qXImag = 66225618180845L;
            set pXReal = 16107719158929L;	    set pXImag = 158176396360L;
            set rXReal = 84317091269572L;	    set rXImag = 68913927530523L;
        }	
        elif (twoTorsion <34){	
            set prime = 18786186952703L;	set twoIndex = 33;
            set qXReal = 17875687864113L;	    set qXImag = 4993293539187L;
            set pXReal = 15557955703090L;	    set pXImag = 6643563577257L;
            set rXReal = 6970555452830L;	    set rXImag = 16281119329153L;
        }	
        elif (twoTorsion <35){	
            set prime = 51539607551L;	set twoIndex = 34;
            set qXReal = 2979037783L;	    set qXImag = 15822585611L;
            set pXReal = 41754988092L;	    set pXImag = 31307813497L;
            set rXReal = 33293398122L;	    set rXImag = 30263981272L;
        }	
        elif (twoTorsion <36){	
            set prime = 18260173718028287L;	set twoIndex = 35;
            set qXReal = 6949506956973172L;	    set qXImag = 3904985659728097L;
            set pXReal = 6313338984629977L;	    set pXImag = 5491934252805014L;
            set rXReal = 11719765575459886L;	    set rXImag = 9256557428033848L;
        }	
        elif (twoTorsion <37){	
            set prime = 16698832846847L;	set twoIndex = 36;
            set qXReal = 14802194921549L;	    set qXImag = 15442521659549L;
            set pXReal = 893699801300L;	    set pXImag = 12038289497529L;
            set rXReal = 13792057318409L;	    set rXImag = 13208222680339L;
        }	
        elif (twoTorsion <38){	
            set prime = 3710851743743L;	set twoIndex = 37;
            set qXReal = 3009116960860L;	    set qXImag = 2791450682285L;
            set pXReal = 3273365228885L;	    set pXImag = 2075973998504L;
            set rXReal = 2245106865850L;	    set rXImag = 2875520875917L;
        }	
        elif (twoTorsion <41){	
            set prime = 824633720831L;	set twoIndex = 38;
            set qXReal = 121413395543L;	    set qXImag = 512409979189L;
            set pXReal = 661099603687L;	    set pXImag = 10046509174L;
            set rXReal = 562958340855L;	    set rXImag = 287512997392L;
        }	
        elif (twoTorsion <42){	
            set prime = 1168651117953810431L;	set twoIndex = 41;
            set qXReal = 148260889640475634L;	    set qXImag = 426166295014974630L;
            set pXReal = 562407188362778641L;	    set pXImag = 880913583554544620L;
            set rXReal = 348500023875156797L;	    set rXImag = 446819776572179964L;
        }	
        elif (twoTorsion <43){	
            set prime = 5111679989929966829567L;	set twoIndex = 42;
            set qXReal = 2394372288170445106555L;	    set qXImag = 807916264125573428125L;
            set pXReal = 2330454243050070974663L;	    set pXImag = 5024601373557805087998L;
            set rXReal = 3439353858424778219998L;	    set rXImag = 4939879462630005601016L;
        }	
        elif (twoTorsion <44){	
            set prime = 26388279066623L;	set twoIndex = 43;
            set qXReal = 23330962176697L;	    set qXImag = 3376670038838L;
            set pXReal = 14115859184115L;	    set pXImag = 11516259629590L;
            set rXReal = 5948738469312L;	    set rXImag = 22415722047934L;
        }	
        elif (twoTorsion <46){	
            set prime = 4274901208793087L;	set twoIndex = 44;
            set qXReal = 2421920895311224L;	    set qXImag = 193246592230925L;
            set pXReal = 370201532541723L;	    set pXImag = 3485843246376599L;
            set rXReal = 1287956271840108L;	    set rXImag = 2059999081080107L;
        }	
        elif (twoTorsion <49){	
            set prime = 1385067991648960511L;	set twoIndex = 46;
            set qXReal = 1332636980894598934L;	    set qXImag = 1361505353586016781L;
            set pXReal = 546967655750782796L;	    set pXImag = 107874896267002357L;
            set rXReal = 575208308065505353L;	    set rXImag = 463564985709997791L;
        }	
        elif (twoTorsion <50){	
            set prime = 4292829748983105583205842943L;	set twoIndex = 49;
            set qXReal = 2402951220143209948805384452L;	    set qXImag = 1539826553813041631537924587L;
            set pXReal = 3562429710104633789906004515L;	    set pXImag = 2288253795332402704863616941L;
            set rXReal = 4171993445904644813759291026L;	    set rXImag = 3997971518325928563983465312L;
        }	
        elif (twoTorsion <51){	
            set prime = 2462343096264818687L;	set twoIndex = 50;
            set qXReal = 194634347411385546L;	    set qXImag = 1694325510301175145L;
            set pXReal = 1617859639075721100L;	    set pXImag = 143243610570635755L;
            set rXReal = 231743695267395364L;	    set rXImag = 2305701040878694605L;
        }	
        elif (twoTorsion < 52){
            set prime = 4172630516011578626876079341567L;
            set qXReal = 347981705370164889049025025203L;
            set qXImag = 386549415249102137819781309762L;
            set pXReal = 4027121263871945649688400720065L;
            set pXImag = 352424858471196915132081710761L;
            set rXReal = 3172623282868588408111857969082L;
            set rXImag = 3827712117102051550066502980090L;
            set twoIndex = 51;
        }
        elif (twoTorsion < 53){
            set prime = 25035783096069471761256476049407L;
            set qXReal = 10760375421385916092704751818172L;
            set qXImag = 13938095491907498455398391390140L;
            set pXReal = 12540098266762389512040230752500L;
            set pXImag = 11447311106702637773368206360618L;
            set rXReal = 16775103929095094720071668935440L;
            set rXImag = 20638780810397474547382925573604L;
            set twoIndex = 52;
        }	
        elif (twoTorsion <55){	
            set prime = 129243464436747803295743L;	set twoIndex = 53;
            set qXReal = 96498281471449034707718L;	    set qXImag = 111408720818999415464963L;
            set pXReal = 30189090245400371550014L;	    set pXImag = 85727300085631444335340L;
            set rXReal = 80092932494919928121293L;	    set rXImag = 111678122187441352893128L;
        }	
        elif (twoTorsion <56){	
            set prime = 108086391056891903L;	set twoIndex = 55;
            set qXReal = 51463832227030786L;	    set qXImag = 96071305785096233L;
            set pXReal = 39091904375727999L;	    set pXImag = 101029883267563573L;
            set rXReal = 29090203471197449L;	    set rXImag = 64535749690770538L;
        }	
        elif (twoTorsion <57){	
            set prime = 17509995351216488447L;	set twoIndex = 56;
            set qXReal = 12271561058478888170L;	    set qXImag = 12190048439551823298L;
            set pXReal = 804599388717638257L;	    set pXImag = 7270831464244083008L;
            set rXReal = 12464684343359244532L;	    set rXImag = 7388612821634566927L;
        }	
        elif (twoTorsion <58){	
            set prime = 689298476995988284243967L;	set twoIndex = 57;
            set qXReal = 417843539520208317064554L;	    set qXImag = 596031073525950566249962L;
            set pXReal = 240577359340942255183821L;	    set pXImag = 611846914417148840600770L;
            set rXReal = 561344971736637594604758L;	    set rXImag = 472483377644539970807089L;
        }	
        elif (twoTorsion <59){	
            set prime = 70039981404865953791L;	set twoIndex = 58;
            set qXReal = 32137864122937061216L;	    set qXImag = 65366311552298159464L;
            set pXReal = 64462915683648056740L;	    set pXImag = 68624035890536069816L;
            set rXReal = 22685665279443380398L;	    set rXImag = 66421997362483968197L;
        }	
        elif (twoTorsion <60){	
            set prime = 919064635994651045658623L;	set twoIndex = 59;
            set qXReal = 263073795269230906181892L;	    set qXImag = 200419423301935195482248L;
            set pXReal = 273256887663822983450040L;	    set pXImag = 568762827349931846213889L;
            set rXReal = 43212990090651708000615L;	    set rXImag = 173129185462729927746047L;
        }	
        elif (twoTorsion <61){	
            set prime = 1838129271989302091317247L;	set twoIndex = 60;
            set qXReal = 1275109399233241471808490L;	    set qXImag = 1024820035770597011568721L;
            set pXReal = 1478429159234861837939293L;	    set pXImag = 309416850134968958574972L;
            set rXReal = 444234080070742514487932L;	    set rXImag = 931754816946833418204547L;
        }	
        elif (twoTorsion <62){	
            set prime = 2305843009213693951L;	set twoIndex = 61;
            set qXReal = 2035378798890061987L;	    set qXImag = 1550152607625418071L;
            set pXReal = 1903856724767140785L;	    set pXImag = 1845619879134167392L;
            set rXReal = 1601839726557852890L;	    set rXImag = 650385411460960169L;
        }	
        elif (twoTorsion <63){	
            set prime = 1120639702477855260671L;	set twoIndex = 62;
            set qXReal = 544264630109008953642L;	    set qXImag = 153588232820374836219L;
            set pXReal = 905255105973409857748L;	    set pXImag = 947043969734654874409L;
            set rXReal = 455697396876337270777L;	    set rXImag = 994543219328010365882L;
        }	
        elif (twoTorsion <64){	
            set prime = 83010348331692982271L;	set twoIndex = 63;
            set qXReal = 65666458681442269005L;	    set qXImag = 79678353032812795295L;
            set pXReal = 44239917398047967283L;	    set pXImag = 33552733099072122804L;
            set rXReal = 22694573703308786915L;	    set rXImag = 19688752824202916365L;
        }	
        elif (twoTorsion <66){	
            set prime = 55340232221128654847L;	set twoIndex = 64;
            set qXReal = 7330809093826706580L;	    set qXImag = 33746464995555146794L;
            set pXReal = 45936233290756754672L;	    set pXImag = 49200576209390547373L;
            set rXReal = 43202195148775308878L;	    set rXImag = 15453085974445621597L;
        }	
        elif (twoTorsion <67){	
            set prime = 9528862145992542041388613631L;	set twoIndex = 66;
            set qXReal = 1474750262949334523325636156L;	    set qXImag = 2368185070739980978442669475L;
            set pXReal = 1922952383836619624913863848L;	    set pXImag = 5297285240047749180623392168L;
            set rXReal = 8875919740784257080328625543L;	    set rXImag = 2437388337825371663989099396L;
        }	
        elif (twoTorsion <68){	
            set prime = 1543675667650791810704955408383L;	set twoIndex = 67;
            set qXReal = 997201866699110670776782811338L;	    set qXImag = 1438266880658310174413928024760L;
            set pXReal = 1397281268278648559671069021983L;	    set pXImag = 1437620980478544387147762983256L;
            set rXReal = 1498000084779032198719842501995L;	    set rXImag = 56260322259437732154692316809L;
        }	
        elif (twoTorsion <69){	
            set prime = 52284565958806815041912831L;	set twoIndex = 68;
            set qXReal = 40308826917695715968148698L;	    set qXImag = 31171291919755744459576139L;
            set pXReal = 24188712633194764744299218L;	    set pXImag = 20313172648851236241556566L;
            set rXReal = 30958425651601346608843044L;	    set rXImag = 38959305786633610570997512L;
        }	
        elif (twoTorsion <70){	
            set prime = 18524108011809501728459464900607L;	set twoIndex = 69;
            set qXReal = 11014914729549791204159618461223L;	    set qXImag = 5577001899973497261413957724079L;
            set pXReal = 12398026985552781411181734520909L;	    set pXImag = 3511252614695169316108239515123L;
            set rXReal = 1478011471760920338051800562608L;	    set rXImag = 3594036133652323728282748663284L;
        }	
        elif (twoTorsion <72){	
            set prime = 31875973759370105192447L;	set twoIndex = 70;
            set qXReal = 5357863282001134031952L;	    set qXImag = 23912106509780083858794L;
            set pXReal = 28221108440198708098619L;	    set pXImag = 19853887627305403648069L;
            set rXReal = 4389374066821074628240L;	    set rXImag = 29161642331022357876187L;
        }	
        elif (twoTorsion <73){	
            set prime = 609847177343522690648871272447L;	set twoIndex = 72;
            set qXReal = 64089954074156224029116005861L;	    set qXImag = 347910377520946511482913720770L;
            set pXReal = 554140802812670309592641582072L;	    set pXImag = 154441786473328675856003755207L;
            set rXReal = 49754482725156440029645921955L;	    set rXImag = 496093775344084633447129421679L;
        }	
        elif (twoTorsion <74){	
            set prime = 1944586762647714253446760787406225407L;	set twoIndex = 73;
            set qXReal = 595214923114889407161444046950275736L;	    set qXImag = 689981734937184704786216243411710905L;
            set pXReal = 440478604316396280422049867990172802L;	    set pXImag = 364508168766646575007907984968899411L;
            set rXReal = 704754581173400958830365875916391316L;	    set rXImag = 1691667328311592266500069934625343349L;
        }	
        elif (twoTorsion <75){	
            set prime = 16004829322203409493388977674125311L;	set twoIndex = 74;
            set qXReal = 14145787513382514437688401917239134L;	    set qXImag = 14175788764346579921267790001899153L;
            set pXReal = 8941827438822421544433341571759809L;	    set pXImag = 2276416231871980095919105461324911L;
            set rXReal = 4755842313688454539242058791637835L;	    set rXImag = 15054112610215536278728732612682341L;
        }	
        elif (twoTorsion <76){	
            set prime = 96028975933220456960333866044751871L;	set twoIndex = 75;
            set qXReal = 64949798264723828440819198292832434L;	    set qXImag = 40836856305486993999854212737946574L;
            set pXReal = 5308297736811266035797386550245367L;	    set pXImag = 79551118502122710039015534466763596L;
            set rXReal = 40471702534341983571898732125203240L;	    set rXImag = 44898417467459442414834220970045484L;
        }	
        elif (twoTorsion <77){	
            set prime = 226673591177742970257407L;	set twoIndex = 76;
            set qXReal = 61086997774577231451929L;	    set qXImag = 22570391816172346487364L;
            set pXReal = 108936888961340859693419L;	    set pXImag = 224687430086467504429896L;
            set rXReal = 61928950994913780425081L;	    set rXImag = 98677614404848528296300L;
        }	
        elif (twoTorsion <78){	
            set prime = 2168345519443636233418208968703L;	set twoIndex = 77;
            set qXReal = 1229809329102663939152269815373L;	    set qXImag = 1073528336690929776121928985228L;
            set pXReal = 767707375270249094645198813020L;	    set pXImag = 867484688782561328597263576164L;
            set rXReal = 1203345434043179063558210506171L;	    set rXImag = 2016730202920199083713469919173L;
        }	
        elif (twoTorsion <79){	
            set prime = 15121106666348626034802011882870808772607L;	set twoIndex = 78;
            set qXReal = 6303647243255689070442355172769810465904L;	    set qXImag = 1711150203032269128880322107984043135294L;
            set pXReal = 317260604412319639806956285013187918378L;	    set pXImag = 2180094782022381141396544126123428618619L;
            set rXReal = 11464665015432048680944386273642582304419L;	    set rXImag = 13200790375593373284078008239540800216275L;
        }	
        elif (twoTorsion <80){	
            set prime = 78060438699970904403055522873343L;	set twoIndex = 79;
            set qXReal = 9099103814411786342500245207945L;	    set qXImag = 14001145822932230040641666520257L;
            set pXReal = 64154750701700616647591064078201L;	    set pXImag = 63675312731328192355426554982723L;
            set rXReal = 53910797400929106634340121067827L;	    set rXImag = 51020658101817067967435275890837L;
        }	
        elif (twoTorsion <81){	
            set prime = 214157582167272714411674959871L;	set twoIndex = 80;
            set qXReal = 38537573802131375258026893401L;	    set qXImag = 117621633455608581895865075649L;
            set pXReal = 27489960459870797277795492152L;	    set pXImag = 207070449034381783315949606779L;
            set rXReal = 54478825372886917490093179861L;	    set rXImag = 186736975900305426698095825932L;
        }	
        elif (twoTorsion <82){	
            set prime = 195845982777569926302400511L;	set twoIndex = 81;
            set qXReal = 34592034774737850102103642L;	    set qXImag = 20750879549856268530962632L;
            set pXReal = 44231314730521768193597490L;	    set pXImag = 191848506214348117644732746L;
            set rXReal = 114011889987861020702122262L;	    set rXImag = 36863449215953175396416778L;
        }	
        elif (twoTorsion <83){	
            set prime = 7709672958021817718820298555391L;	set twoIndex = 82;
            set qXReal = 5888922466974969008128453390854L;	    set qXImag = 4126361821707844326424621392203L;
            set pXReal = 7265605673732067084549249422698L;	    set pXImag = 5290616711387783006830034764918L;
            set rXReal = 7471077833005720253659961957121L;	    set rXImag = 3286559653974047381875218409943L;
        }	
        elif (twoTorsion <84){	
            set prime = 190362295259797968365933297663L;	set twoIndex = 83;
            set qXReal = 180417926767384581315818869781L;	    set qXImag = 1992615514951965756714552022L;
            set pXReal = 50820525068559082610591912072L;	    set pXImag = 189474323218085659331938389452L;
            set rXReal = 54416961518041525898104680141L;	    set rXImag = 188970356094143254793381471591L;
        }	
        elif (twoTorsion <85){	
            set prime = 1820993913992921257914479237589368831L;	set twoIndex = 84;
            set qXReal = 1432793227159271609227086965924371879L;	    set qXImag = 341008930112873318145435666468937690L;
            set pXReal = 894871019109595789203131396378051265L;	    set pXImag = 315746545317562944509997196778320335L;
            set rXReal = 1206860414614422290682208996292778803L;	    set rXImag = 1744144065597433789302235029549492139L;
        }	
        elif (twoTorsion <86){	
            set prime = 20559127888058180583520796147711L;	set twoIndex = 85;
            set qXReal = 14944812800038458933820351806161L;	    set qXImag = 12550968197397870333304224446011L;
            set pXReal = 18337469392314377345228054926702L;	    set pXImag = 13465986445260224269913999514436L;
            set rXReal = 4584789692754369190763433130359L;	    set rXImag = 15294690310180864241229410306614L;
        }	
        elif (twoTorsion < 91){	
            set prime = 5310018253203358388078621456810599514111L;	set twoIndex = 86;
            set qXReal = 3196514773025466825002478027639817266297L;	    set qXImag = 4201044234167008014663581888167454655483L;
            set pXReal = 3239114306514985223758062202092304290073L;	    set pXImag = 3477755011863096407398851832477622317664L;
            set rXReal = 3253803330537010001323245599364166384247L;	    set rXImag = 4108849725243901481095350643568877226193L;
        }	
        elif (twoTorsion < 128){
            set prime = 3887237936338808897317857226010584482932750535805108223L;
            set qXReal = 998775931727511462167621423543015228722729785033265230L;
            set qXImag = 1229842274887130713723578054343844450980843286372577272L;
            set pXReal = 3529692006983830146569643951471747719224539157480987689L;
            set pXImag = 2987154053440573511279525556248982633620409142190952457L;
            set rXReal = 1429586273551882408638154815340735028350063622843233778L;
            set rXImag = 3171054172864605496529583688999818379042838516413500723L;
            set twoIndex = 91;
        }
        elif (twoTorsion < 217){
            set prime = 150890214974780584126857431087264183671206865243463858730925256539725436551167L;
            set qXReal = 31402848085043898121664235299682325060386277103305040779618047608273717694112L;
            set qXImag = 135131040680559649173015213631315898026519380146414580806034521408299682845092L;
            set pXReal = 70585036836460582711144824932778247323325749082052530626502269001400150390709L;
            set pXImag = 11114418831704671514358127175613210193447689217435087494712836287047470267356L;
            set rXReal = 102190101391824902521046417963542206479218536003004129224514092764139941669148L;
            set rXImag = 146902564783616710955353779541370694086127414573541686038268438926540453947000L;
            set twoIndex = 128;
        } elif (twoTorsion < 0xFA) {
            //SIKE 434 parameters
            set prime = 24439423661345221551909145011457493619085780243761596511325807336205221239331976725970216671828618445898719026692884939342314733567L;
            set pXReal =  8633131302536015373065425580178973814526244742660764898957635611033517358603093513483897324469034427019598357249425684820405193836L;
            set pXImag =  1640555213321637736080614728970921962714590288563692816952785470842808462670732196555713644986698688787353020078064569199240185333L;
            set qXReal =  2634539327592482918121599540115765431217195093350648632832477775508933673747596362667240890051240463853167541162279343167040310088L;
            set qXImag = 18590308952679468489364793668589003541299106140709579196186461020066893645141198854487503147226318730158493210982567772716162869840L;
            set rXReal = 10548244869191429978994573331033429460802791853191679921432716242390096998215982561051229194803656270150791181542353263212179039510L;
            set rXImag = 17623338845092751517427595119320347017334966146230013113905734683582704966390296970846105400364294574370981828797535336936167097772L;
            set twoIndex = 216;
        } elif (twoTorsion < 0x131) {
            //SIKE 503 parameters
            set prime = 0x004066F541811E1E6045C6BDDA77A4D01B9BF6C87B7E7DAF13085BDA2211E7A0ABFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFL;
            set twoIndex = 0xFA;
            set pXReal = 0x0002ED31A03825FA14BC1D92C503C061D843223E611A92D7C5FBEC0F2C915EE7EEE73374DF6A1161EA00CDCB786155E21FD38220C3772CE670BC68274B851678L;
            set pXImag = 0x001EE4E4E9448FBBAB4B5BAEF280A99B7BF86A1CE05D55BD603C3BA9D7C08FD8DE7968B49A78851FFBC6D0A17CB2FA1B57F3BABEF87720DD9A489B5581F915D2L;
            set qXReal = 0x00325CF6A8E2C6183A8B9932198039A7F965BA8587B67925D08D809DBF9A69DE1B621F7F134FA2DAB82FF5A2615F92CC71419FFFAAF86A290D604AB167616461L;
            set qXImag = 0x003E7B0494C8E60A8B72308AE09ED34845B34EA0911E356B77A11872CF7FEEFF745D98D0624097BC1AD7CD2ADF7FFC2C1AA5BA3C6684B964FA555A0715E57DB1L;
            set rXReal = 0x003D24CF1F347F1DA54C1696442E6AFC192CEE5E320905E0EAB3C9D3FB595CA26C154F39427A0416A9F36337354CF1E6E5AEDD73DF80C710026D49550AC8CE9L;
            set rXImag = 0x0006869EA28E4CEE05DCEE8B08ACD59775D03DAA0DC8B094C85156C212C23C72CB2AB2D2D90D46375AA6D66E58E44F8F219431D3006FDED7993F51649C029498L;
        } elif (twoTorsion < 0x174) {
            // SIKE 610 parameters
            set prime =  0x000000027BF6A768819010C251E7D88CB255B2FA10C4252A9AE7BF45048FF9ABB1784DE8AA5AB02E6E01FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFL;
            set pXReal = 0x00000001B368BC6019B46CD802129209B3E65B98BC64A92BC4DB2F9F3AC96B97A1B9C124DF549B528F18BEECB1666D27D47530435E84221272F3A97FB80527D8F8A359F8F1598D365744CA3070A5F26CL;
            set pXImag = 0x00000001459685DCA7112D1F6030DBC98F2C9CBB41617B6AD913E6523416CCBD8ED9C7841D97DF83092B9B3F2AF00D62E08DAD8FA743CBCCCC1782BE0186A3432D3C97C37CA16873BEDE01F0637C1AA2L;
            set qXReal = 0x25DA39EC90CDFB9BC0F772CDA52CB8B5A9F478D7AF8DBBA0AEB3E52432822DD88C38F4E3AEC0746E56149F1FE89707C77F8BA4134568629724F4A8E34B06BFE5C5E66E0867EC38B283798B8AL;
            set qXImag = 0x00000002250E1959256AE502428338CB4715399551AEC78D8935B2DC73FCDCFBDB1A0118A2D3EF03489BA6F637B1C7FEE7E5F31340A1A537B76B5B736B4CDD284918918E8C986FC02741FB8C98F0A0EDL;
            set rXReal = 0x00000001B36A006D05F9E370D5078CCA54A16845B2BFF737C865368707C0DBBE9F5A62A9B9C79ADF11932A9FA4806210E25C92DB019CC146706DFBC7FA2638ECC4343C1E390426FAA7F2F07FDA163FB5L;
            set rXImag = 0x0000000183C9ABF2297CA69699357F58FED92553436BBEBA2C3600D89522E7009D19EA5D6C18CFF993AA3AA33923ED93592B0637ED0B33ADF12388AE912BC4AE4749E2DF3C3292994DCF37747518A992L;
            set twoIndex = 0x131;
        } else {
            // SIKE 751 parameters
            set prime =  0x00006FE5D541F71C0E12909F97BADC668562B5045CB25748084E9867D6EBE876DA959B1A13F7CC76E3EC968549F878A8EEAFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFL;
            set pXReal = 0x00004514F8CC94B140F24874F8B87281FA6004CA5B3637C68AC0C0BDB29838051F385FBBCC300BBB24BFBBF6710D7DC8B29ACB81E429BD1BD5629AD0ECAD7C90622F6BB801D0337EE6BC78A7F12FDCB09DECFAE8BFD643C89C3BAC1D87F8B6FAL;
            set pXImag = 0x0000158ABF500B5914B3A96CED5FDB37D6DD925F2D6E4F7FEA3CC16E1085754077737EA6F8CC74938D971DA289DCF2435BCAC1897D2627693F9BB167DC01BE34AC494C60B8A0F65A28D7A31EA0D54640653A8099CE5A84E4F0168D818AF02041L;
            set qXReal = 0x00001723D2BFA01A78BF4E39E3A333F8A7E0B415A17F208D3419E7591D59D8ABDB7EE6D2B2DFCB21AC29A40F837983C0F057FD041AD93237704F1597D87F074F682961A38B5489D1019924F8A0EF5E4F1B2E64A7BA536E219F5090F76276290EL;
            set qXImag = 0x00002569D7EAFB6C60B244EF49E05B5E23F73C4F44169A7E02405E90CEB680CB0756054AC0E3DCE95E2950334262CC973235C2F87D89500BCD465B078BD0DEBDF322A2F86AEDFDCFEE65C09377EFBA0C5384DD837BEDB710209FBC8DDB8C35C7L;
            set rXReal = 0x00006066E07F3C0D964E8BC963519FAC8397DF477AEA9A067F3BE343BC53C883AF29CCF008E5A30719A29357A8C33EB3600CD078AF1C40ED5792763A4D213EBDE44CC623195C387E0201E7231C529A15AF5AB743EE9E7C9C37AF3051167525BBL;
            set rXImag = 0x000050E30C2C06494249BC4A144EB5F31212BD05A2AF0CB3064C322FC3604FC5F5FE3A08FB3A02B05A48557E15C992254FFC8910B72B8E1328B4893CDCFBFC003878881CE390D909E39F83C5006E0AE979587775443483D13C65B107FADA5165L;
            set twoIndex = 0x174;
        }
        let pX = Fp2ElementClassical(
            prime,
            pXReal,
            pXImag
        );
        let qX = Fp2ElementClassical(
            prime,
            qXReal,
            qXImag
        );
        let rX = Fp2ElementClassical(
            prime,
            rXReal,
            rXImag
        );
        let zPoint = Fp2ElementClassical(prime, 1L, 0L);
        let pointP = ECPointMontgomeryXZClassical(pX, zPoint);
        let pointQ = ECPointMontgomeryXZClassical(qX, zPoint);
        let pointR = ECPointMontgomeryXZClassical(rX, zPoint);
        return SIKEParams(
            prime, 
            twoIndex, 
            pointP,
            pointQ,
            pointR
        );
    }

    /// # Summary
    /// Returns a two torsion size such that the 
    /// SIKE parameters with that two torsion have the 
    /// required bit size.
    /// If no such two torsion exists, returns -1.
    function SIKETwoTorsionForBitSize(nBits : Int) : Int {
        for (twoTorsion in 4 .. 3 * nBits){
            let SIKEps = GetSIKEParams(twoTorsion);
            if (BitSizeL(SIKEps::prime) == nBits){
                return twoTorsion;
            }
        }
        return -1;
    }




    ///////////////// MONTGOMERY (X : Z) POINT DOUBLING /////////////////
    /// # Summary
    /// Out-of-place doubling of an elliptic curve point in (X : Z) coordinates
    /// in a qubit register, on a curve given by $(A_{24}^+, C_{24})$ coordinates
    /// given in another qubit register.
    ///
    /// # Inputs
    /// ## point
    /// Qubit register encoding the (X : Z) coordinates to be doubled.
    /// ## curve
    /// Qubit register encoding the curve containing `point`, as 
    /// $(A_{24}^+,C_{24})$ coordinates.
    /// ## doublepoint
    /// Qubit register assumed to be initialized to $\ket{0}$.
    /// This registers will be returned containing the doubled point.
    ///
    /// # Operations
    /// This can test : 
    ///		* DoubleECPointMontgomeryXZ
    operation EllipticCurveMontgomeryFormXZPointDoublingTestHelper (
        PointDoubler : ((ECPointMontgomeryXZ,ECCoordsMontgomeryFormAPlusC,ECPointMontgomeryXZ)=>Unit is Ctl),
        point : ECPointMontgomeryXZClassical,
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        nQubits : Int
    ) : Unit {
      body (...) {
            // Bookkeeping and qubit allocation
            using (register = Qubit[12*nQubits]) {
                let modulus = point::x::modulus;
                let zeropoint = ECPointMontgomeryXZClassical(
                    Fp2ElementClassical(modulus, 0L,0L),
                    Fp2ElementClassical(modulus, 0L,0L)
                );

                // Write to qubit registers
                mutable qpoint1 = CreateECPointMontgomeryXZ(point,register[0..4*nQubits - 1]);
                mutable qpoint2 = CreateECPointMontgomeryXZ(zeropoint,register[4*nQubits..8*nQubits - 1]);
                mutable qcurve  = CreateECCoordsMontgomeryFormAPlusC(curve,register[8*nQubits..12*nQubits - 1]);

                // Run test
                PointDoubler(qpoint1,qcurve,qpoint2);
 
                // Compute expected classical result
                let expected = PointDoubleMontgomeryXZClassical(point,curve);

                // Check results
                mutable actualpoint1 = MeasureECPointMontgomeryXZ(qpoint1);
                mutable actualcurve = MeasureECCoordsMontgomeryFormAPlusC(qcurve);
                mutable actualpoint2 = MeasureECPointMontgomeryXZ(qpoint2);
                Fact(
                    IsEqualMontgomeryXZClassical(point,actualpoint1), 
                    $"Input point : Expected ({point::x::real} + {point::x::imag}i,{point::z::real} + {point::z::imag}i)
                    , got ({actualpoint1::x::real} + {actualpoint1::x::imag}i,{actualpoint1::z::real} + {actualpoint1::z::imag}i)"
                );
                Fact(
                    IsEqualFp2Element(actualcurve::a24Plus,curve::a24Plus) and IsEqualFp2Element(actualcurve::c24,curve::c24), 
                    $"Input curve : Expected ({actualcurve::a24Plus::real} + {actualcurve::a24Plus::imag}i,{actualcurve::c24::real} + {actualcurve::c24::imag}i)
                    , got ({curve::a24Plus::real} + {curve::a24Plus::imag}i,{curve::c24::real} + {curve::c24::imag}i)"
                );
               Fact(
                    IsEqualMontgomeryXZClassical(expected,actualpoint2), 
                    $"Output : Expected ({expected::x::real} + {expected::x::imag}i,{expected::z::real} + {expected::z::imag}i)
                    , got ({actualpoint2::x::real} + {actualpoint2::x::imag}i,{actualpoint2::z::real} + {actualpoint2::z::imag}i)"
                );

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        set qpoint1 = CreateECPointMontgomeryXZ(point,register[0..4*nQubits - 1]);
                        set qpoint2 = CreateECPointMontgomeryXZ(zeropoint,register[4*nQubits..8*nQubits - 1]);
                        set qcurve  = CreateECCoordsMontgomeryFormAPlusC(curve,register[8*nQubits..12*nQubits - 1]);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled PointDoubler) (controls, (qpoint1,qcurve,qpoint2));

                        // Check results
                        set actualpoint1 = MeasureECPointMontgomeryXZ(qpoint1);
                        set actualcurve = MeasureECCoordsMontgomeryFormAPlusC(qcurve);
                        set actualpoint2 = MeasureECPointMontgomeryXZ(qpoint2);
                        Fact(
                            IsEqualMontgomeryXZClassical(point,actualpoint1), 
                            $"Control 0 : Input point : Expected ({point::x::real} + {point::x::imag}i,{point::z::real} + {point::z::imag}i)
                            , got ({actualpoint1::x::real} + {actualpoint1::x::imag}i,{actualpoint1::z::real} + {actualpoint1::z::imag}i)"
                        );
                        Fact(
                            IsEqualFp2Element(actualcurve::a24Plus,curve::a24Plus) and IsEqualFp2Element(actualcurve::c24,curve::c24), 
                            $"Control 0 : Input curve : Expected ({actualcurve::a24Plus::real} + {actualcurve::a24Plus::imag}i,{actualcurve::c24::real} + {actualcurve::c24::imag}i)
                            , got ({curve::a24Plus::real} + {curve::a24Plus::imag}i,{curve::c24::real} + {curve::c24::imag}i)"
                        );
                        
                       Fact(
                            IsEqualMontgomeryXZClassical(zeropoint,actualpoint2), 
                            $"Control 0 : Output : Expected ({zeropoint::x::real} + {zeropoint::x::imag}i,{zeropoint::z::real} + {zeropoint::z::imag}i)
                            , got ({actualpoint2::x::real} + {actualpoint2::x::imag}i,{actualpoint2::z::real} + {actualpoint2::z::imag}i)"
                        );

                        // Write to qubit registers
                        set qpoint1 = CreateECPointMontgomeryXZ(point,register[0..4*nQubits - 1]);
                        set qpoint2 = CreateECPointMontgomeryXZ(zeropoint,register[4*nQubits..8*nQubits - 1]);
                        set qcurve  = CreateECCoordsMontgomeryFormAPlusC(curve,register[8*nQubits..12*nQubits - 1]);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled PointDoubler) (controls, (qpoint1,qcurve,qpoint2));

                        // Check results
                        set actualpoint1 = MeasureECPointMontgomeryXZ(qpoint1);
                        set actualcurve = MeasureECCoordsMontgomeryFormAPlusC(qcurve);
                        set actualpoint2 = MeasureECPointMontgomeryXZ(qpoint2);
                        Fact(
                            IsEqualMontgomeryXZClassical(point,actualpoint1), 
                            $"Control 1 : Input point : Expected ({point::x::real} + {point::x::imag}i,{point::z::real} + {point::z::imag}i)
                            , got ({actualpoint1::x::real} + {actualpoint1::x::imag}i,{actualpoint1::z::real} + {actualpoint1::z::imag}i)"
                        );
                        Fact(
                            IsEqualFp2Element(actualcurve::a24Plus,curve::a24Plus) and IsEqualFp2Element(actualcurve::c24,curve::c24), 
                            $"Control 1 : Input curve : Expected ({actualcurve::a24Plus::real} + {actualcurve::a24Plus::imag}i,{actualcurve::c24::real} + {actualcurve::c24::imag}i)
                            , got ({curve::a24Plus::real} + {curve::a24Plus::imag}i,{curve::c24::real} + {curve::c24::imag}i)"
                        );
                        
                       Fact(
                            IsEqualMontgomeryXZClassical(expected,actualpoint2), 
                            $"Control 1 : Output : Expected ({expected::x::real} + {expected::x::imag}i,{expected::z::real} + {expected::z::imag}i)
                            , got ({actualpoint2::x::real} + {actualpoint2::x::imag}i,{actualpoint2::z::real} + {actualpoint2::z::imag}i)"
                        );

                        ResetAll(controls);
                    }
                }
            }
        }
    }


    operation ECPointMontgomeryXZPointDoublerSmallTest() : Unit {
        let nQubits = 10;
        let modulus = 863L;
        let E6=ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(modulus,8L,0L),
            Fp2ElementClassical(modulus,4L,0L)		
        );
        let Q2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,472L,767L),
            Fp2ElementClassical(modulus,1L,0L)
        );
        let P2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,399L,796L),
            Fp2ElementClassical(modulus,1L,0L)
        );
        let R2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,195L,302L),
            Fp2ElementClassical(modulus,1L,0L)
        );
        let Q3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,697L,741L),
            Fp2ElementClassical(modulus,1L,0L)
        );
        let P3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,104L,298L),
            Fp2ElementClassical(modulus,1L,0L)
        );
        let R3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,347L,383L),
            Fp2ElementClassical(modulus,1L,0L)
        );
        let zeroPoint = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,0L,0L),
            Fp2ElementClassical(modulus,0L,0L)
        );
        EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ,Q2,E6,nQubits);
        EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ,P2,E6,nQubits);
        EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ,R2,E6,nQubits);
        EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ,Q3,E6,nQubits);
        EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ,P3,E6,nQubits);
        EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ,R3,E6,nQubits);
    }

    // Requires more than 12 hours currently
    //operation ECPointMontgomeryXZPointDoublerLargeTest() : Unit {
    //		//SIKE - 434 parameters
    //		// > 12 hours 
    //		let nQubits = 434;
    //let modulus = 24439423661345221551909145011457493619085780243761596511325807336205221239331976725970216671828618445898719026692884939342314733567L;
    //let E6 = ECCoordsMontgomeryFormAPlusCClassical(
    //    Fp2ElementClassical(modulus, 6L, 0L),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);
    //let Q2 = ECPointMontgomeryXZClassical(
    //    Fp2ElementClassical(modulus, 
    //        8633131302536015373065425580178973814526244742660764898957635611033517358603093513483897324469034427019598357249425684820405193836L,
    //        1640555213321637736080614728970921962714590288563692816952785470842808462670732196555713644986698688787353020078064569199240185333L
    //	  ),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);
    //let P2 = ECPointMontgomeryXZClassical(
    //    Fp2ElementClassical(modulus, 
    //        2634539327592482918121599540115765431217195093350648632832477775508933673747596362667240890051240463853167541162279343167040310088L,
    //        18590308952679468489364793668589003541299106140709579196186461020066893645141198854487503147226318730158493210982567772716162869840L
    //    ),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);
    //let R2 = ECPointMontgomeryXZClassical(
    //    Fp2ElementClassical(modulus, 
    //        10548244869191429978994573331033429460802791853191679921432716242390096998215982561051229194803656270150791181542353263212179039510L,
    //        17623338845092751517427595119320347017334966146230013113905734683582704966390296970846105400364294574370981828797535336936167097772L
    //    ),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);
    //let Q3 = ECPointMontgomeryXZClassical(
    //    Fp2ElementClassical(modulus, 
    //        13106015910647201458426811493288965923311702902321179794984306791335898269651901670809619116119997952683697617529379507339288983622L,
    //        0L
    //    ),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);
    //let P3 = ECPointMontgomeryXZClassical(
    //    Fp2ElementClassical(modulus, 
    //        5822289030790821842647204127346110197186614331916510409554480418611145246532692679762948023941031185216358707524703325193156147113L,
    //        0L
    //    ),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);
    //let R3 = ECPointMontgomeryXZClassical(
    //    Fp2ElementClassical(modulus, 
    //        19978714732817982296321998790126652405475699311529669091328949981490769847281914491438519436155586335833863255694913096932863948652L,
    //        14167827257511306746606440016400170231086622175754382579855491498256779752299521404090563911050166061448571907478184141518856743652L
    //    ),
    //    Fp2ElementClassical(modulus, 1L, 0L)
    //);

    //EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ, Q2, E6, nQubits);
    //EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ, P2, E6, nQubits);
    //EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ, R2, E6, nQubits);
    //EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ, Q3, E6, nQubits);
    //EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ, P3, E6, nQubits);
    //EllipticCurveMontgomeryFormXZPointDoublingTestHelper(DoubleECPointMontgomeryXZ, R3, E6, nQubits);
    //	}

    operation ECPointMontgomeryXZPointDoublerRandomTestHelper(PointDoubler : ((ECPointMontgomeryXZ,ECCoordsMontgomeryFormAPlusC,ECPointMontgomeryXZ)=>Unit is Ctl),
        nQubits : Int,nTests : Int) : Unit {
        for (roundnum in 0..nTests - 1){
            let modulus = RandomFp2Modulus(nQubits);

            let point = ECPointMontgomeryXZClassical(
                RandomFp2ElementClassical(modulus),
                RandomFp2ElementClassical(modulus)
            );
            let curve = ECCoordsMontgomeryFormAPlusCClassical(
                RandomFp2ElementClassical(modulus),
                RandomFp2ElementClassical(modulus)
            );
            EllipticCurveMontgomeryFormXZPointDoublingTestHelper(PointDoubler,point,curve,nQubits);
        }
    }

    operation ECPointMontgomeryXZPointDoublerRandomTextReversible() : Unit {
        let nQubits = 8;
        let nTests=500;
        ECPointMontgomeryXZPointDoublerRandomTestHelper(DoubleECPointMontgomeryXZ,nQubits,nTests);
    }

    ///////////////// OPEN POINT DOUBLING /////////////////
    ///
    /// # Summary
    /// Out-of-place doubling of an elliptic curve point in (X : Z) coordinates
    /// in a qubit register, on a curve given by $(A_{24}^+, C_{24})$ coordinates
    /// given in another qubit register. Requires clean ancillas which are 
    /// returned dirty.
    ///
    /// # Inputs
    /// ## point
    /// Qubit register encoding the (X : Z) coordinates to be doubled.
    /// ## curve
    /// Qubit register encoding the curve containing `point`, as 
    /// $(A_{24}^+,C_{24})$ coordinates.
    /// ## ancillas
    /// Clean ancillas which are returned dirty.
    /// ## blankOutput
    /// Qubit register assumed to be initialized to $\ket{0}$.
    /// This registers will be returned containing the doubled point.
    ///
    /// # Operations
    /// This can test:
    ///		* DoubleECPointMontgomeryXZOpen
    operation DoubleECPointMontgomeryXZOpenTestHelper(
        Doubler : ( (ECPointMontgomeryXZ, ECCoordsMontgomeryFormAPlusC, Qubit[], ECPointMontgomeryXZ) => Unit is Ctl + Adj), 
        point : ECPointMontgomeryXZClassical,
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        nQubits : Int,
        nAncillas : Int 
        ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[12 * nQubits + nAncillas]){
                let modulus = point::x::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                let zeroPoint = ECPointMontgomeryXZClassical(zeroFp2, zeroFp2);
                mutable actualPoint = zeroPoint;
                mutable actualCurve = curve;
                mutable result = zeroPoint;
                mutable ancilla = 0L;
                let ancillas = register[12 * nQubits .. 12 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable qPoint = CreateECPointMontgomeryXZ(point, register[0 .. 4 * nQubits - 1]);
                mutable qCurve = CreateECCoordsMontgomeryFormAPlusC(curve, register[4 * nQubits .. 8 * nQubits - 1]);
                mutable qResult = CreateECPointMontgomeryXZ(zeroPoint, register[8 * nQubits .. 12 * nQubits - 1]);

                // Run test
                Doubler(qPoint, qCurve, ancillas, qResult);

                // Compute expected classical result
                let doubledPoint = PointDoubleMontgomeryXZClassical(point, curve);

                // Check results
                set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                Fact(IsEqualMontgomeryXZClassical(actualPoint, point), $"Input: Expected {point}, got {actualPoint}");
                set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                Fact(IsEqualECCoordsMontgomeryFormAPlusC(actualCurve, curve), $"Input: Expected {curve}, got {actualCurve}");
                set result = MeasureECPointMontgomeryXZ(qResult);
                Fact(IsEqualMontgomeryXZClassical(result, doubledPoint), $"Result : Expected {doubledPoint}, got {result}");

                // Rewrite results to measured qubit reigsters
                EncodeECPointMontgomeryXZ(actualPoint, qPoint);
                EncodeECCoordsMontgomeryFormAPlusC(actualCurve, qCurve);
                EncodeECPointMontgomeryXZ(doubledPoint, qResult);

                // Uncompute test
                (Adjoint Doubler)(qPoint, qCurve, ancillas, qResult);

                // Check results
                set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                Fact(IsEqualMontgomeryXZClassical(actualPoint, point), $"Uncomputed : Input Q : Expected {point}, got {actualPoint}");
                set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                Fact(IsEqualECCoordsMontgomeryFormAPlusC(actualCurve, curve), $"Input: Expected {curve}, got {actualCurve}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureECPointMontgomeryXZ(qResult);
                Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Uncomputed : Result : Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(point, qPoint);
                        EncodeECCoordsMontgomeryFormAPlusC(curve, qCurve);

                        // Run test
                        (Controlled Doubler)(controls, (qPoint, qCurve, ancillas, qResult));

                        // Check results 
                        set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                        Fact(IsEqualMontgomeryXZClassical(actualPoint, point), $"Control 0 : Input Q : Expected {point}, got {actualPoint}");
                        set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(IsEqualECCoordsMontgomeryFormAPlusC(actualCurve, curve), $"Control 0 : Input: Expected {curve}, got {actualCurve}");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Control 0 : Result : Expected {0}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeECPointMontgomeryXZ(actualPoint, qPoint);
                        EncodeECCoordsMontgomeryFormAPlusC(actualCurve, qCurve);

                        // Uncompute test
                        (Adjoint Controlled Doubler)(controls, (qPoint, qCurve, ancillas, qResult));

                        // Check results
                        set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                        Fact(IsEqualMontgomeryXZClassical(actualPoint, point), $"Control 0 : Uncomputed : Input Q : Expected {point}, got {actualPoint}");
                        set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(IsEqualECCoordsMontgomeryFormAPlusC(actualCurve, curve), $"Control 0 : Input: Expected {curve}, got {actualCurve}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0 : Ancilla not returned to 0");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Control 0 : Uncomputed : Result : Expected {0}, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeECPointMontgomeryXZ(point, qPoint);
                        EncodeECCoordsMontgomeryFormAPlusC(curve, qCurve);

                        // Run test
                        (Controlled Doubler)(controls, (qPoint, qCurve, ancillas, qResult));

                        // Check results
                        set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                        Fact(IsEqualMontgomeryXZClassical(actualPoint, point), $"Control 1 : Input Q : Expected {point}, got {actualPoint}");
                        set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(IsEqualECCoordsMontgomeryFormAPlusC(actualCurve, curve), $"Control 1 : Input: Expected {curve}, got {actualCurve}");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, doubledPoint), $"Control 1 : Result : Expected {doubledPoint}, got {result}");

                        // Rewrite results to qubit registers
                        EncodeECPointMontgomeryXZ(actualPoint, qPoint);
                        EncodeECCoordsMontgomeryFormAPlusC(actualCurve, qCurve);
                        EncodeECPointMontgomeryXZ(doubledPoint, qResult);

                        // Uncompute test
                        (Adjoint Controlled Doubler)(controls, (qPoint, qCurve, ancillas, qResult));

                        // Check results
                        set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                        Fact(IsEqualMontgomeryXZClassical(actualPoint, point), $"Control 1 : Uncomputed : Input Q : Expected {point}, got {actualPoint}");
                        set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(IsEqualECCoordsMontgomeryFormAPlusC(actualCurve, curve), $"Control 1 : Input: Expected {curve}, got {actualCurve}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1 : Ancilla not returned to 0");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Control 1 : Uncomputed : Result : Expected {doubledPoint}, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation DoubleECPointMontgomeryXZTest () : Unit {
        let nQubits = 8;
        let modulus = 167L;
        let point = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus, 101L, 8L),
            Fp2ElementClassical(modulus, 8L, 42L)
        );
        let curve = ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(modulus, 117L, 38L),
            Fp2ElementClassical(modulus, 39L, 31L)
        );
        let (nAncillas, _) = AncillaCountDoubleECPoint(nQubits);
        DoubleECPointMontgomeryXZOpenTestHelper(DoubleECPointMontgomeryXZOpen, point, curve, nQubits, nAncillas);
    }

    operation DoubleECPointMontgomeryXZRandomTestHelper (
        Doubler : (
            (
                ECPointMontgomeryXZ, 
                ECCoordsMontgomeryFormAPlusC, 
                Qubit[], 
                ECPointMontgomeryXZ
            ) => Unit is Ctl + Adj
        ),
        nQubits : Int,
        nAncillas : Int,
        nTests : Int) : Unit {
        mutable idxTest = 0;
        repeat {
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let zFp2 = RandomFp2ElementClassical(modulus);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
            let cFp2 = RandomInvertibleFp2ElementClassical(modulus);
            let aFp2 = RandomFp2ElementClassical(modulus);
            let point = ECPointMontgomeryXZClassical(xFp2, zFp2);
            let curve = ECCoordsMontgomeryFormAPlusCClassical(aFp2, cFp2);
            DoubleECPointMontgomeryXZOpenTestHelper(Doubler, point, curve, nQubits, nAncillas);
            set idxTest = idxTest + 1;
        } until (idxTest >= nTests);
    }

    operation DoubleECPointOpenRandomTest () : Unit {
        let nQubits = 8;
        let (nAncillas, _) = AncillaCountDoubleECPoint(nQubits);
        let nTests = 100;
        DoubleECPointMontgomeryXZRandomTestHelper(DoubleECPointMontgomeryXZOpen, nQubits, nAncillas, nTests);
    }

    ///////////////// OPEN DIFFERENTIAL MONTGOMERY (X,Z) POINT ADDITION /////////////////
    ///
    /// # Summary
    /// Given a classical point P and 
    /// qubit registers encoding points Q and Q-P,
    /// computes Q+P in a blank output qubit register. 
    /// Uses clean ancillas which are returned dirty.
    ///
    /// # Inputs
    // ## pointP
    /// Classical point P
    /// ## pointQ
    /// Qubit register encoding the point Q
    /// ## pointQminP
    /// Qubit register encoding the point Q - P
    /// ## ancillas
    /// Clean ancillas which are returned dirty
    /// ## outputPoint
    /// Qubit register assumed to be blank (all zeros)
    /// which will contain the output point
    ///
    /// # Operations
    /// This can test:
    ///		* DifferentialAddECPointMontgomeryXZOpen
    operation DifferentialAdderECPointMontgomeryXZOpenHelper(
        DiffAdder : ( (ECPointMontgomeryXZClassical, ECPointMontgomeryXZ, ECPointMontgomeryXZ, Qubit[], ECPointMontgomeryXZ) => Unit is Ctl + Adj), 
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointR : ECPointMontgomeryXZClassical,
        nQubits : Int,
        nAncillas : Int 
        ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[12 * nQubits + nAncillas]){
                let modulus = pointP::x::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                let zeroPoint = ECPointMontgomeryXZClassical(zeroFp2, zeroFp2);
                mutable actualQ = zeroPoint;
                mutable actualR = zeroPoint;
                mutable result = zeroPoint;
                mutable ancilla = 0L;
                let ancillas = register[12 * nQubits .. 12 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable qPointQ = CreateECPointMontgomeryXZ(pointQ, register[0 .. 4 * nQubits - 1]);
                mutable qPointR = CreateECPointMontgomeryXZ(pointR, register[4 * nQubits .. 8 * nQubits - 1]);
                mutable qResult = CreateECPointMontgomeryXZ(zeroPoint, register[8 * nQubits .. 12 * nQubits - 1]);

                // Run test
                DiffAdder(pointP, qPointQ, qPointR, ancillas, qResult);

                // Compute expected classical result
                let pointSum = DifferentialAddECPointMontgomeryXZClassical(pointP, pointQ, pointR);

                // Check results
                set actualQ = MeasureECPointMontgomeryXZ(qPointQ);
                Fact(IsEqualMontgomeryXZClassical(actualQ, pointQ), $"Input Q : Expected {pointQ}, got {actualQ}");
                set actualR = MeasureECPointMontgomeryXZ(qPointR);
                Fact(IsEqualMontgomeryXZClassical(actualR, pointR), $"Input R : Expected {pointR}, got {actualR}");
                set result = MeasureECPointMontgomeryXZ(qResult);
                Fact(IsEqualMontgomeryXZClassical(result, pointSum), $"Result : Expected {pointSum}, got {result}");

                // Rewrite results to measured qubit reigsters
                EncodeECPointMontgomeryXZ(actualQ, qPointQ);
                EncodeECPointMontgomeryXZ(actualR, qPointR);
                EncodeECPointMontgomeryXZ(pointSum, qResult);

                // Uncompute test
                (Adjoint DiffAdder)(pointP, qPointQ, qPointR, ancillas, qResult);

                // Check results
                set actualQ = MeasureECPointMontgomeryXZ(qPointQ);
                Fact(IsEqualMontgomeryXZClassical(actualQ, pointQ), $"Uncomputed : Input Q : Expected {pointQ}, got {actualQ}");
                set actualR = MeasureECPointMontgomeryXZ(qPointR);
                Fact(IsEqualMontgomeryXZClassical(actualR, pointR), $"Uncomputed : Input R : Expected {pointR}, got {actualR}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureECPointMontgomeryXZ(qResult);
                Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Uncomputed : Result : Expected {0}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(pointQ, qPointQ);
                        EncodeECPointMontgomeryXZ(pointR, qPointR);

                        // Run test
                        (Controlled DiffAdder)(controls, (pointP, qPointQ, qPointR, ancillas, qResult));

                        // Check results 
                        set actualQ = MeasureECPointMontgomeryXZ(qPointQ);
                        Fact(IsEqualMontgomeryXZClassical(actualQ, pointQ), $"Control 0 : Input Q : Expected {pointQ}, got {actualQ}");
                        set actualR = MeasureECPointMontgomeryXZ(qPointR);
                        Fact(IsEqualMontgomeryXZClassical(actualR, pointR), $"Control 0 : Input R : Expected {pointR}, got {actualR}");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Control 0 : Result : Expected {0}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeECPointMontgomeryXZ(actualQ, qPointQ);
                        EncodeECPointMontgomeryXZ(actualR, qPointR);

                        // Uncompute test
                        (Adjoint Controlled DiffAdder)(controls, (pointP, qPointQ, qPointR, ancillas, qResult));

                        // Check results
                        set actualQ = MeasureECPointMontgomeryXZ(qPointQ);
                        Fact(IsEqualMontgomeryXZClassical(actualQ, pointQ), $"Control 0 : Uncomputed : Input Q : Expected {pointQ}, got {actualQ}");
                        set actualR = MeasureECPointMontgomeryXZ(qPointR);
                        Fact(IsEqualMontgomeryXZClassical(actualR, pointR), $"Control 0 : Uncomputed : Input R : Expected {pointR}, got {actualR}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0 : Ancilla not returned to 0");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Control 0 : Uncomputed : Result : Expected {0}, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeECPointMontgomeryXZ(pointQ, qPointQ);
                        EncodeECPointMontgomeryXZ(pointR, qPointR);

                        // Run test
                        (Controlled DiffAdder)(controls, (pointP, qPointQ, qPointR, ancillas, qResult));

                        // Check results
                        set actualQ = MeasureECPointMontgomeryXZ(qPointQ);
                        Fact(IsEqualMontgomeryXZClassical(actualQ, pointQ), $"Control 1 : Input Q : Expected {pointQ}, got {actualQ}");
                        set actualR = MeasureECPointMontgomeryXZ(qPointR);
                        Fact(IsEqualMontgomeryXZClassical(actualR, pointR), $"Control 1 : Input R : Expected {pointR}, got {actualR}");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, pointSum), $"Control 1 : Result : Expected {pointSum}, got {result}");

                        // Rewrite results to qubit registers
                        EncodeECPointMontgomeryXZ(actualQ, qPointQ);
                        EncodeECPointMontgomeryXZ(actualR, qPointR);
                        EncodeECPointMontgomeryXZ(pointSum, qResult);

                        // Uncompute test
                        (Adjoint Controlled DiffAdder)(controls, (pointP, qPointQ, qPointR, ancillas, qResult));

                        // Check results
                        set actualQ = MeasureECPointMontgomeryXZ(qPointQ);
                        Fact(IsEqualMontgomeryXZClassical(actualQ, pointQ), $"Control 1 : Uncomputed : Input Q : Expected {pointQ}, got {actualQ}");
                        set actualR = MeasureECPointMontgomeryXZ(qPointR);
                        Fact(IsEqualMontgomeryXZClassical(actualR, pointR), $"Control 1 : Uncomputed : Input R : Expected {pointR}, got {actualR}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1 : Ancilla not returned to 0");
                        set result = MeasureECPointMontgomeryXZ(qResult);
                        Fact(IsEqualMontgomeryXZClassical(result, zeroPoint), $"Control 1 : Uncomputed : Result : Expected {pointSum}, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    
    operation DifferentialAdderOpenTestHelper (
        DiffAdder : (
            (
                ECPointMontgomeryXZClassical, 
                ECPointMontgomeryXZ, 
                ECPointMontgomeryXZ, 
                Qubit[], 
                ECPointMontgomeryXZ
            ) => Unit is Ctl + Adj
        ),
        nQubits : Int,
        nAncillas : Int,
        nTests : Int) : Unit {
        mutable idxTest = 0;
        repeat {
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            let zFp2 = RandomFp2ElementClassical(modulus);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
            //Must ensure that x^2z is invertible as an element of F_p^2
            let x2z = MultiplyFp2ElementClassical(SquareFp2ElementClassical(xFp2), zFp2);
            let normX2Z = (x2z::real ^ 2 + x2z::imag ^ 2) % modulus;	
            if (GreatestCommonDivisorL(normX2Z,modulus) == 1L){
                //Find a curve containing this point
                let curve = MontgomeryXZCurveOfPointClassical(xFp2, yFp2, zFp2);
                //Start with random P, Q = O, and R = Q - P = - P
                mutable pointP = ECPointMontgomeryXZClassical(xFp2, zFp2);
                mutable pointQ = ECPointMontgomeryXZClassical(zeroFp2, zeroFp2);
                mutable pointR = pointP;
                // Pick random n - bit s, compute 
                //  P < - 2^n P
                //  Q < - sP
                //  R = Q - P
                let coefficient = RandomBigInt(modulus);
                set (pointP, pointQ, pointR) = PointLadderClassical(curve, pointP, pointQ, pointR, coefficient);
                //Differential point adder is ill - defined for (X : Z) = (0 : 0), so we 
                // avoid that case
                let zeroPoint = ECPointMontgomeryXZClassical(zeroFp2, zeroFp2);
                if (not (IsEqualMontgomeryXZClassical(pointP, zeroPoint) 
                        or IsEqualMontgomeryXZClassical(pointQ, zeroPoint)
                        or IsEqualMontgomeryXZClassical(pointR, zeroPoint))){
                    DifferentialAdderECPointMontgomeryXZOpenHelper(
                        DiffAdder,
                        pointP,
                        pointQ,
                        pointR,
                        nQubits,
                        nAncillas
                    );
                    // Only increment for successful tests
                    set idxTest = idxTest + 1;
                }
            }
        } until (idxTest >= nTests);
    }

    operation DifferentialECPointAdderOpenRandomTest () : Unit {
        let nQubits = 8;
        let (nAncillas, _) = AncillaCountECPointDiffAddition(nQubits);
        let nTests = 100;
        DifferentialAdderOpenTestHelper(DifferentialAddECPointMontgomeryXZOpen, nQubits, nAncillas, nTests);
    }
    

    ///////////////// POINT LADDER FOR MONTGOMERY (X : Z) POINTS /////////////////
    ///
    /// # Summary
    /// Computes P + sQ for classical
    /// elliptic curve points P and Q
    /// and quantum coefficient s.
    ///
    /// # Inputs
    /// ## curve
    /// The curve containing P and Q
    /// ## pointP
    /// The point P
    /// ## pointQ
    /// The point Q
    /// ## pointQminP
    /// The point Q - P
    /// ## coefficient
    /// The qubit register containing s
    /// ## outputPoint
    /// Blank qubit register which will contain
    /// P + sQ
    ///
    /// # Operations
    /// This can test:
    ///		* MontgomeryXZPointLadderNaive
    operation PointLadderTestHelper(
        PointLadder : ((
            ECCoordsMontgomeryFormAPlusCClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            LittleEndian,
            ECPointMontgomeryXZ
        ) => Unit is Ctl),
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointQminP : ECPointMontgomeryXZClassical,
        coefficient : BigInt,
        nQubits : Int
    ) : Unit {
        body (...){
            // Bookkeeping and qubit allocation
            let coefficientSize = Max([BitSizeL(coefficient), nQubits]);
            using (register = Qubit[4 * nQubits + coefficientSize]) {
                mutable actualCoefficient = 0L;
                let modulus = curve::a24Plus::modulus;
                let zeroPoint = ECPointMontgomeryXZClassical(
                    Fp2ElementClassical(modulus, 0L,0L),
                    Fp2ElementClassical(modulus, 0L,0L)
                );
                mutable actualPoint = zeroPoint;
                mutable qPoint = CreateECPointMontgomeryXZ(zeroPoint, register[0..4 * nQubits - 1]);
                mutable qCoefficient = LittleEndian(register[4 * nQubits .. 4 * nQubits + coefficientSize - 1]);

                // Write to qubit registers
                ApplyXorInPlaceL(coefficient, qCoefficient);
                
                // Run test
                PointLadder(curve, pointP, pointQ, pointQminP, qCoefficient, qPoint);
 
                // Compute expected classical result
                let (_, expected, _) = PointLadderClassical(curve, pointP, pointQ, pointQminP, coefficient);

                // Check results
                set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                set actualCoefficient = MeasureBigInteger(qCoefficient);
                Fact(actualCoefficient == coefficient, "Input : Expected {coefficient}, got {actualCoefficient}");
                Fact(
                    IsEqualMontgomeryXZClassical(expected, actualPoint), 
                    $"Output : Expected ({expected::x::real} + {expected::x::imag}i,{expected::z::real} + {expected::z::imag}i)
                    , got ({actualPoint::x::real} + {actualPoint::x::imag}i,{actualPoint::z::real} + {actualPoint::z::imag}i)"
                );

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(coefficient, qCoefficient);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled PointLadder) (controls, (curve, pointP, pointQ, pointQminP, qCoefficient, qPoint));

                        // Check results
                        set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                        set actualCoefficient = MeasureBigInteger(qCoefficient);
                        Fact(actualCoefficient == coefficient, "Control 0: Input : Expected {coefficient}, got {actualCoefficient}");
                        Fact(
                            IsEqualMontgomeryXZClassical(actualPoint, zeroPoint), 
                            $"Control 0: Output : Expected ({zeroPoint::x::real} + {zeroPoint::x::imag}i,{zeroPoint::z::real} + {zeroPoint::z::imag}i)
                            , got ({actualPoint::x::real} + {actualPoint::x::imag}i,{actualPoint::z::real} + {actualPoint::z::imag}i)"
                        );

                        // Write to qubit registers
                        ApplyXorInPlaceL(coefficient, qCoefficient);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled PointLadder) (controls, (curve, pointP, pointQ, pointQminP, qCoefficient, qPoint));

                        // Check results
                         set actualPoint = MeasureECPointMontgomeryXZ(qPoint);
                        set actualCoefficient = MeasureBigInteger(qCoefficient);
                        Fact(actualCoefficient == coefficient, "Control 1: Input : Expected {coefficient}, got {actualCoefficient}");
                        Fact(
                            IsEqualMontgomeryXZClassical(expected, actualPoint), 
                            $"Control 1: Output : Expected ({expected::x::real} + {expected::x::imag}i,{expected::z::real} + {expected::z::imag}i)
                            , got ({actualPoint::x::real} + {actualPoint::x::imag}i,{actualPoint::z::real} + {actualPoint::z::imag}i)"
                        );

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation PointLadderRandomTestHelper (
        PointLadder : ((
            ECCoordsMontgomeryFormAPlusCClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            LittleEndian,
            ECPointMontgomeryXZ
        ) => Unit is Ctl),
        nQubits : Int,
        nTests : Int) : Unit {
        let twoTorsion = SIKETwoTorsionForBitSize(nQubits);
        Fact(twoTorsion > -1, $"No SIKE parameters included for bit size nQubits");
        let SIKEps = GetSIKEParams(twoTorsion);
        let curve = ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(SIKEps::prime, 8L, 0L),
            Fp2ElementClassical(SIKEps::prime, 4L, 0L)
        );
        for (idxTest in 0..nTests - 1){
            let coefficient = RandomBigInt(2L^twoTorsion);
            Message($"Finished {idxTest} tests");
            PointLadderTestHelper(
                PointLadder,
                curve, 
                SIKEps::pointP,
                SIKEps::pointQ,
                SIKEps::pointR,
                coefficient,
                nQubits
            );
        }
    }

    operation PointLadderRandomTest() : Unit {
        let nQubits = 9; // minimum size, each test takes about 
        //let nQubits = 5;
        let nTests = 100;
        PointLadderRandomTestHelper(MontgomeryXZPointLadderLowMemory, nQubits, nTests);
    }

    ///////////////// ITERATED POINT DOUBLING ///////////////// 
    ///
    /// # Summary
    /// Writes [2^n]P, for an elliptic curve
    /// point P and an integer n, to a blank
    /// qubit register.
    ///
    /// # Inputs
    /// ## curve
    /// Qubit register containing the curve
    /// containing P
    /// ## point
    /// The point P
    /// ## nDoublings
    /// The number of times to double P
    /// ## outputPoint
    /// The blank register to contain the output
    ///
    /// # Operations
    /// This can test:
    ///		* IteratedPointDouble
    ///		* IteratedPointDoubleHighMemory
    ///		* IteratedPointDoubleLowMemory
    operation IteratedPointDoublingTestHelper(
        IteratedDoubler : ((
            ECCoordsMontgomeryFormAPlusC,
            ECPointMontgomeryXZ,
            Int,
            ECPointMontgomeryXZ
        ) => Unit is Ctl),
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        point : ECPointMontgomeryXZClassical,
        nDoublings : Int,
        nQubits : Int
    ) : Unit {
        body (...){
            // Bookkeeping and qubit allocation
            using (register = Qubit[12 * nQubits]) {
                mutable actualCoefficient = 0L;
                let modulus = curve::a24Plus::modulus;
                let zeroPoint = ECPointMontgomeryXZClassical(
                    Fp2ElementClassical(modulus, 0L,0L),
                    Fp2ElementClassical(modulus, 0L,0L)
                );
                mutable inputPoint = zeroPoint;
                mutable resultPoint = zeroPoint;
                mutable actualCurve = curve;

                // Write to qubit registers
                mutable qPoint = CreateECPointMontgomeryXZ(point, register[0..4 * nQubits - 1]);
                mutable qCurve = CreateECCoordsMontgomeryFormAPlusC(curve, register[4 * nQubits .. 8 * nQubits - 1]);
                mutable outputPoint = CreateECPointMontgomeryXZ(zeroPoint, register[8 * nQubits .. 12 * nQubits - 1]);

                // Run test
                IteratedDoubler(qCurve, qPoint, nDoublings, outputPoint);
 
                // Compute expected classical result
                mutable doubledPoint = point;
                for (idx in 1..nDoublings){
                    set doubledPoint = PointDoubleMontgomeryXZClassical(doubledPoint, curve);
                }

                // Check results
                set inputPoint = MeasureECPointMontgomeryXZ(qPoint);
                set resultPoint = MeasureECPointMontgomeryXZ(outputPoint);
                set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                Fact(
                    IsEqualMontgomeryXZClassical(point, inputPoint), 
                    $"Input point : Expected ({point::x::real} + {point::x::imag}i,{point::z::real} + {point::z::imag}i)
                    , got ({inputPoint::x::real} + {inputPoint::x::imag}i,{inputPoint::z::real} + {inputPoint::z::imag}i)"
                );
                Fact(
                    IsEqualECCoordsMontgomeryFormAPlusC(curve, actualCurve), 
                    $"Input curve : Expected ({curve::a24Plus::real} + {curve::a24Plus::imag}i,{curve::c24::real} + {curve::c24::imag}i)
                    , got ({actualCurve::a24Plus::real} + {actualCurve::a24Plus::imag}i,{actualCurve::c24::real} + {actualCurve::c24::imag}i)"
                );
                 Fact(
                    IsEqualMontgomeryXZClassical(doubledPoint, resultPoint), 
                    $"Output : Expected ({doubledPoint::x::real} + {doubledPoint::x::imag}i,{doubledPoint::z::real} + {doubledPoint::z::imag}i)
                    , got ({resultPoint::x::real} + {resultPoint::x::imag}i,{resultPoint::z::real} + {resultPoint::z::imag}i)"
                );

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(point, qPoint);
                        EncodeECCoordsMontgomeryFormAPlusC(curve, qCurve);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled IteratedDoubler) (controls, (qCurve, qPoint, nDoublings, outputPoint));

                        // Check results
                        set inputPoint = MeasureECPointMontgomeryXZ(qPoint);
                        set resultPoint = MeasureECPointMontgomeryXZ(outputPoint);
                        set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(
                            IsEqualMontgomeryXZClassical(point, inputPoint), 
                            $"Control 0: Input point : Expected ({point::x::real} + {point::x::imag}i,{point::z::real} + {point::z::imag}i)
                            , got ({inputPoint::x::real} + {inputPoint::x::imag}i,{inputPoint::z::real} + {inputPoint::z::imag}i)"
                        );
                        Fact(
                            IsEqualECCoordsMontgomeryFormAPlusC(curve, actualCurve), 
                            $"Control 0: Input curve : Expected ({curve::a24Plus::real} + {curve::a24Plus::imag}i,{curve::c24::real} + {curve::c24::imag}i)
                            , got ({actualCurve::a24Plus::real} + {actualCurve::a24Plus::imag}i,{actualCurve::c24::real} + {actualCurve::c24::imag}i)"
                        );
                         Fact(
                            IsEqualMontgomeryXZClassical(zeroPoint, resultPoint), 
                            $"Control 0: Output : Expected ({zeroPoint::x::real} + {zeroPoint::x::imag}i,{zeroPoint::z::real} + {zeroPoint::z::imag}i)
                            , got ({resultPoint::x::real} + {resultPoint::x::imag}i,{resultPoint::z::real} + {resultPoint::z::imag}i)"
                        );

                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(point, qPoint);
                        EncodeECCoordsMontgomeryFormAPlusC(curve, qCurve);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                        (Controlled IteratedDoubler) (controls, (qCurve, qPoint, nDoublings, outputPoint));

                        // Check results
                        set inputPoint = MeasureECPointMontgomeryXZ(qPoint);
                        set resultPoint = MeasureECPointMontgomeryXZ(outputPoint);
                        set actualCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(
                            IsEqualMontgomeryXZClassical(point, inputPoint), 
                            $"Control 1: Input point : Expected ({point::x::real} + {point::x::imag}i,{point::z::real} + {point::z::imag}i)
                            , got ({inputPoint::x::real} + {inputPoint::x::imag}i,{inputPoint::z::real} + {inputPoint::z::imag}i)"
                        );
                        Fact(
                            IsEqualECCoordsMontgomeryFormAPlusC(curve, actualCurve), 
                            $"Control 1: Input curve : Expected ({curve::a24Plus::real} + {curve::a24Plus::imag}i,{curve::c24::real} + {curve::c24::imag}i)
                            , got ({actualCurve::a24Plus::real} + {actualCurve::a24Plus::imag}i,{actualCurve::c24::real} + {actualCurve::c24::imag}i)"
                        );
                         Fact(
                            IsEqualMontgomeryXZClassical(doubledPoint, resultPoint), 
                            $"Control 1: Output : Expected ({doubledPoint::x::real} + {doubledPoint::x::imag}i,{doubledPoint::z::real} + {doubledPoint::z::imag}i)
                            , got ({resultPoint::x::real} + {resultPoint::x::imag}i,{resultPoint::z::real} + {resultPoint::z::imag}i)"
                        );

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation IteratedPointDoublerRandomTestHelper (
        IteratedDoubler : ((
            ECCoordsMontgomeryFormAPlusC,
            ECPointMontgomeryXZ,
            Int,
            ECPointMontgomeryXZ
        ) => Unit is Ctl),
        nQubits : Int,
        nTests : Int) : Unit {
        mutable idxTest = 0;
        repeat {
            let modulus = RandomFp2Modulus(nQubits);
            let xFp2 = RandomFp2ElementClassical(modulus);
            let yFp2 = RandomFp2ElementClassical(modulus);
            let zFp2 = RandomFp2ElementClassical(modulus);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
            //Must ensure that x^2z is invertible as an element of F_p^2
            let x2z = MultiplyFp2ElementClassical(SquareFp2ElementClassical(xFp2), zFp2);
            let normX2Z = (x2z::real ^ 2 + x2z::imag ^ 2) % modulus;	
            if (GreatestCommonDivisorL(normX2Z, modulus) == 1L){
                //Find a curve containing this point
                let curve = MontgomeryXZCurveOfPointClassical(xFp2, yFp2, zFp2);
                //Start with random P
                let point = ECPointMontgomeryXZClassical(xFp2, zFp2);
                
                let nDoublings = Max([Microsoft.Quantum.Random.DrawRandomInt(0, nQubits - 1),1]);
                IteratedPointDoublingTestHelper(IteratedDoubler, curve, point, nDoublings, nQubits);
                set idxTest = idxTest + 1;
            }
        } until (idxTest >= nTests);
    }

    operation IteratedPointDoublerRandomTest() : Unit {
        let nQubits = 8; // each test takes about 10s
        //let nQubits = 5;
        let nTests = 100;
        IteratedPointDoublerRandomTestHelper(IteratedPointDoubleLowMemory, nQubits, nTests);
    }

    ///////////////// OPEN J-INVARIANT COMPUTATION/////////////////
    ///
    /// # Summary
    /// Computes the j-invariant of a quantum elliptic curve E,
    /// given in projective (A : C) coordinates. Uses clean 
    /// ancilla which are returned dirty.
    ///
    /// # Inputs
    /// ## curve
    /// The curve E 
    /// ## ancillas
    /// Clean ancillas which are returned dirty.
    /// ## blankOutput
    /// Empty qubit register which will be returned containing j(E)
    ///
    /// # Operations
    /// This can test:
    ///		* GetJInvariantACOpen
    operation JInvariantACOpenTestHelper(
        JInvariant : (
            (ECCoordsMontgomeryFormAC, 
            Qubit[], 
            Fp2MontModInt
        ) => Unit is Ctl + Adj), 
        curve : ECCoordsMontgomeryFormACClassical,
        nQubits : Int,
        nAncillas : Int 
        ) : Unit {
        body (...) {
            // Bookkeeping and ancilla allocation
            using (register = Qubit[6 * nQubits + nAncillas]){
                let modulus = curve::aCoeff::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                let zeroCurve = ECCoordsMontgomeryFormACClassical(zeroFp2, zeroFp2);
                mutable actualCurve = zeroCurve;
                mutable result = zeroFp2;
                mutable ancilla = 0L;
                let ancillas = register[6 * nQubits .. 6 * nQubits + nAncillas - 1];
                let ancillaLE = LittleEndian(ancillas);
            
                // Write to qubit registers
                mutable qCurve = CreateECCoordsMontgomeryFormAC(curve, register[0 .. 4 * nQubits - 1]);
                mutable qResult = CreateFp2MontModInt(zeroFp2, register[4 * nQubits .. 6 * nQubits - 1]);

                // Compute expected classical result
                let jInvariant = JInvariantClassical(curve);

                // Run test
                JInvariant(qCurve, ancillas, qResult);

                // Check results
                set actualCurve = MeasureECCoordsMontgomeryFormAC(qCurve);
                Fact(IsEqualFp2Element(actualCurve::aCoeff, curve::aCoeff)
                    and IsEqualFp2Element(actualCurve::cCoeff, curve::cCoeff), 
                    $"Input curve : Expected {curve}, got {actualCurve}");
                set result = MeasureFp2MontModInt(qResult);
                Fact(IsEqualFp2Element(result, jInvariant), $"Result : Expected {jInvariant}, got {result}");

                // Rewrite results to measured qubit reigsters
                EncodeECCoordsMontgomeryFormAC(curve, qCurve);
                EncodeFp2MontModInt(jInvariant, qResult);
                // Uncompute test
                (Adjoint JInvariant)(qCurve, ancillas, qResult);

                // Check results
                set actualCurve = MeasureECCoordsMontgomeryFormAC(qCurve);
                Fact(IsEqualFp2Element(actualCurve::aCoeff, curve::aCoeff)
                    and IsEqualFp2Element(actualCurve::cCoeff, curve::cCoeff), 
                    $"Uncomputed: Input curve : Expected {curve}, got {actualCurve}");
                set ancilla = MeasureBigInteger(ancillaLE);
                Fact(ancilla == 0L, $"Ancilla not returned to 0");
                set result = MeasureFp2MontModInt(qResult);
                Fact(IsEqualFp2Element(result, zeroFp2), $"Uncomputed :Result : Expected {zeroFp2}, got {result}");

                 for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeECCoordsMontgomeryFormAC(curve, qCurve);

                        // Run test
                        (Controlled  JInvariant)(controls, (qCurve, ancillas, qResult));

                        // Check results 
                        set actualCurve = MeasureECCoordsMontgomeryFormAC(qCurve);
                        Fact(IsEqualFp2Element(actualCurve::aCoeff, curve::aCoeff)
                            and IsEqualFp2Element(actualCurve::cCoeff, curve::cCoeff), 
                            $"Control 0: Input curve : Expected {curve}, got {actualCurve}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not kept at 0");
                        set result = MeasureFp2MontModInt(qResult);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Result : Expected {zeroFp2}, got {result}");

                        // Rewrite results to measured qubit registers
                        EncodeECCoordsMontgomeryFormAC(curve, qCurve);

                        // Uncompute test
                        (Adjoint Controlled  JInvariant)(controls, (qCurve, ancillas, qResult));

                        // Check results
                        set actualCurve = MeasureECCoordsMontgomeryFormAC(qCurve);
                        Fact(IsEqualFp2Element(actualCurve::aCoeff, curve::aCoeff)
                            and IsEqualFp2Element(actualCurve::cCoeff, curve::cCoeff), 
                            $"Control 0: Uncomputed: Input curve : Expected {curve}, got {actualCurve}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 0: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(qResult);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 0: Uncomputed :Result : Expected {zeroFp2}, got {result}");

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Write to qubit register
                        EncodeECCoordsMontgomeryFormAC(curve, qCurve);

                        // Run test
                        (Controlled  JInvariant)(controls, (qCurve, ancillas, qResult));

                        // Check results
                        set actualCurve = MeasureECCoordsMontgomeryFormAC(qCurve);
                        Fact(IsEqualFp2Element(actualCurve::aCoeff, curve::aCoeff)
                            and IsEqualFp2Element(actualCurve::cCoeff, curve::cCoeff), 
                            $"Control 1: Input curve : Expected {curve}, got {actualCurve}");
                        set result = MeasureFp2MontModInt(qResult);
                        Fact(IsEqualFp2Element(result, jInvariant), $"Control 1: Result : Expected {jInvariant}, got {result}");

                        // Rewrite results to qubit registers
                        EncodeECCoordsMontgomeryFormAC(curve, qCurve);
                        EncodeFp2MontModInt(jInvariant, qResult);

                        // Uncompute test
                        (Adjoint Controlled  JInvariant)(controls, (qCurve, ancillas, qResult));

                        // Check results
                        set actualCurve = MeasureECCoordsMontgomeryFormAC(qCurve);
                        Fact(IsEqualFp2Element(actualCurve::aCoeff, curve::aCoeff)
                            and IsEqualFp2Element(actualCurve::cCoeff, curve::cCoeff), 
                            $"Control 1: Uncomputed: Input curve : Expected {curve}, got {actualCurve}");
                        set ancilla = MeasureBigInteger(ancillaLE);
                        Fact(ancilla == 0L, $"Control 1: Ancilla not returned to 0");
                        set result = MeasureFp2MontModInt(qResult);
                        Fact(IsEqualFp2Element(result, zeroFp2), $"Control 1: Uncomputed :Result : Expected {zeroFp2}, got {result}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }
    

    operation JInvariantACRandomTestHelper (
        JInvariant : (
                (ECCoordsMontgomeryFormAC, 
                Qubit[], 
                Fp2MontModInt
            ) => Unit is Ctl + Adj), 
        nQubits : Int,
        nAncilla : Int,
        nTests : Int
    ) : Unit {
        for (idxTest in 0.. nTests - 1){
            mutable modulus = RandomFp2Modulus(nQubits);
            let curve = RandomECCoordsMontgomeryAC(modulus);
            JInvariantACOpenTestHelper(JInvariant, curve, nQubits, nAncilla);
        }
    }

    operation JInvariantACRandomTest () : Unit {
        let nQubits = 12;
        let nTests = 100;
        let (nAncilla, _) = AncillaCountJInvariantAC(nQubits);
        JInvariantACRandomTestHelper(GetJInvariantACOpen, nQubits, nAncilla, nTests);
    }


    ///////////////// TWO ISOGENY OF A POINT ///////////////// 
    ///
    /// # Summary
    /// From a point P of exact order 2 and another point Q
    /// not in <P>, computes f(Q) for the isogeny f with kernel
    /// equal to <P>. 
    ///
    /// # Inputs
    /// ## kernelPoint
    /// The point P of exact order 2.
    /// ## targetPoint
    /// The point Q as input to the isogeny.
    /// ## outputPoint
    /// Blank qubit register to store f(Q)
    ///
    /// # Operations
    /// This can test:
    ///		* TwoIsogenyOfPoint
    operation TwoIsogenyOfPointTestHelper(
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ
        ) => Unit is Ctl),
        kernelPoint : ECPointMontgomeryXZClassical,
        inputPoint : ECPointMontgomeryXZClassical,
        nQubits : Int
    ) : Unit {
        body (...){
            // Bookkeeping and qubit allocation
            using (register = Qubit[12 * nQubits]) {
                mutable actualCoefficient = 0L;
                let modulus = kernelPoint::x::modulus;
                let zeroPoint = ECPointMontgomeryXZClassical(
                    Fp2ElementClassical(modulus, 0L,0L),
                    Fp2ElementClassical(modulus, 0L,0L)
                );
                mutable actualKernelPoint = zeroPoint;
                mutable actualInputPoint = zeroPoint;
                mutable resultPoint = zeroPoint;

                // Write to qubit registers
                mutable qKernelPoint = CreateECPointMontgomeryXZ(kernelPoint, register[0..4 * nQubits - 1]);
                mutable qInputPoint = CreateECPointMontgomeryXZ(inputPoint, register[4 * nQubits .. 8 * nQubits - 1]);
                mutable outputPoint = CreateECPointMontgomeryXZ(zeroPoint, register[8 * nQubits .. 12 * nQubits - 1]);

                // Run test
                Isogeny(qKernelPoint, qInputPoint, outputPoint);
 
                // Compute expected classical result
                let imagePoint = TwoIsogenyAtPointMontgomeryXZClassical(kernelPoint, inputPoint);

                // Check results
                set actualKernelPoint = MeasureECPointMontgomeryXZ(qKernelPoint);
                set actualInputPoint = MeasureECPointMontgomeryXZ(qInputPoint);
                set resultPoint = MeasureECPointMontgomeryXZ(outputPoint);
                Fact(
                    IsEqualMontgomeryXZClassical(kernelPoint, actualKernelPoint), 
                    $"Kernel point : Expected ({kernelPoint::x::real} + {kernelPoint::x::imag}i,{kernelPoint::z::real} + {kernelPoint::z::imag}i)
                    , got ({actualKernelPoint::x::real} + {actualKernelPoint::x::imag}i,{actualKernelPoint::z::real} + {actualKernelPoint::z::imag}i)"
                );
                Fact(
                    IsEqualMontgomeryXZClassical(inputPoint, actualInputPoint), 
                    $"Input point : Expected ({inputPoint::x::real} + {inputPoint::x::imag}i,{inputPoint::z::real} + {inputPoint::z::imag}i)
                    , got ({actualInputPoint::x::real} + {actualInputPoint::x::imag}i,{actualInputPoint::z::real} + {actualInputPoint::z::imag}i)"
                );
                 Fact(
                    IsEqualMontgomeryXZClassical(imagePoint, resultPoint), 
                    $"Output : Expected ({imagePoint::x::real} + {imagePoint::x::imag}i,{imagePoint::z::real} + {imagePoint::z::imag}i)
                    , got ({resultPoint::x::real} + {resultPoint::x::imag}i,{resultPoint::z::real} + {resultPoint::z::imag}i)"
                );

                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(kernelPoint, qKernelPoint);
                        EncodeECPointMontgomeryXZ(inputPoint, qInputPoint);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled Isogeny) (controls, (qKernelPoint, qInputPoint, outputPoint));

                        // Check results
                        set actualKernelPoint = MeasureECPointMontgomeryXZ(qKernelPoint);
                        set actualInputPoint = MeasureECPointMontgomeryXZ(qInputPoint);
                        set resultPoint = MeasureECPointMontgomeryXZ(outputPoint);
                        Fact(
                            IsEqualMontgomeryXZClassical(kernelPoint, actualKernelPoint), 
                            $"Kernel point : Expected ({kernelPoint::x::real} + {kernelPoint::x::imag}i,{kernelPoint::z::real} + {kernelPoint::z::imag}i)
                            , got ({actualKernelPoint::x::real} + {actualKernelPoint::x::imag}i,{actualKernelPoint::z::real} + {actualKernelPoint::z::imag}i)"
                        );
                        Fact(
                            IsEqualMontgomeryXZClassical(inputPoint, actualInputPoint), 
                            $"Input point : Expected ({inputPoint::x::real} + {inputPoint::x::imag}i,{inputPoint::z::real} + {inputPoint::z::imag}i)
                            , got ({actualInputPoint::x::real} + {actualInputPoint::x::imag}i,{actualInputPoint::z::real} + {actualInputPoint::z::imag}i)"
                        );
                         Fact(
                            IsEqualMontgomeryXZClassical(zeroPoint, resultPoint), 
                            $"Output : Expected ({zeroPoint::x::real} + {zeroPoint::x::imag}i,{zeroPoint::z::real} + {zeroPoint::z::imag}i)
                            , got ({resultPoint::x::real} + {resultPoint::x::imag}i,{resultPoint::z::real} + {resultPoint::z::imag}i)"
                        );

                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(kernelPoint, qKernelPoint);
                        EncodeECPointMontgomeryXZ(inputPoint, qInputPoint);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                         (Controlled Isogeny) (controls, (qKernelPoint, qInputPoint, outputPoint));

                        // Check results
                        set actualKernelPoint = MeasureECPointMontgomeryXZ(qKernelPoint);
                        set actualInputPoint = MeasureECPointMontgomeryXZ(qInputPoint);
                        set resultPoint = MeasureECPointMontgomeryXZ(outputPoint);
                        Fact(
                            IsEqualMontgomeryXZClassical(kernelPoint, actualKernelPoint), 
                            $"Kernel point : Expected ({kernelPoint::x::real} + {kernelPoint::x::imag}i,{kernelPoint::z::real} + {kernelPoint::z::imag}i)
                            , got ({actualKernelPoint::x::real} + {actualKernelPoint::x::imag}i,{actualKernelPoint::z::real} + {actualKernelPoint::z::imag}i)"
                        );
                        Fact(
                            IsEqualMontgomeryXZClassical(inputPoint, actualInputPoint), 
                            $"Input point : Expected ({inputPoint::x::real} + {inputPoint::x::imag}i,{inputPoint::z::real} + {inputPoint::z::imag}i)
                            , got ({actualInputPoint::x::real} + {actualInputPoint::x::imag}i,{actualInputPoint::z::real} + {actualInputPoint::z::imag}i)"
                        );
                         Fact(
                            IsEqualMontgomeryXZClassical(imagePoint, resultPoint), 
                            $"Output : Expected ({imagePoint::x::real} + {imagePoint::x::imag}i,{imagePoint::z::real} + {imagePoint::z::imag}i)
                            , got ({resultPoint::x::real} + {resultPoint::x::imag}i,{resultPoint::z::real} + {resultPoint::z::imag}i)"
                        );

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation SmallIsogenyOfPointTestHelper(
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ
        ) => Unit is Ctl)
    ):Unit {
        let nQubits = 10;
        let p = 863L;
        let e2=5;
        let E0=ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(p, 8L,0L),
            Fp2ElementClassical(p, 4L,0L)		
        );
        let Q2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 472L,767L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let P2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 399L,796L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let R2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 679L, 665L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let Q3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 697L,741L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let P3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 104L,298L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let R3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 347L,383L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let zeroPoint = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 0L,0L),
            Fp2ElementClassical(p, 0L,0L)
        );

        let pPoints = DoubledPointArray(P2, E0, e2);
        let qPoints = DoubledPointArray(Q2, E0, e2);
        let rPoints = DoubledPointArray(R2, E0, e2);

        let twoTorsions = [pPoints[e2 - 1], qPoints[e2 - 1], rPoints[e2 - 1]];
        let threePoints = [P3, Q3, R3];

        for (idxTwo in 0..2){
            for (idxThree in 0..2){
                TwoIsogenyOfPointTestHelper(Isogeny, twoTorsions[idxTwo], threePoints[idxThree], nQubits);
            }
        }
    }

    operation SmallIsogenyOfPointTest() : Unit {
        SmallIsogenyOfPointTestHelper(TwoIsogenyOfPoint);
    }

    operation LargeIsogenyOfPointTestHelper(
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ
        ) => Unit is Ctl)
    ) : Unit {
        //SIKE - 434 parameters
        let nQubits = 434;
        let e2 = 216;
        let modulus = 24439423661345221551909145011457493619085780243761596511325807336205221239331976725970216671828618445898719026692884939342314733567L;
        let E6 = ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(modulus, 6L, 0L),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let Q2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                8633131302536015373065425580178973814526244742660764898957635611033517358603093513483897324469034427019598357249425684820405193836L,
                1640555213321637736080614728970921962714590288563692816952785470842808462670732196555713644986698688787353020078064569199240185333L
              ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let P2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                2634539327592482918121599540115765431217195093350648632832477775508933673747596362667240890051240463853167541162279343167040310088L,
                18590308952679468489364793668589003541299106140709579196186461020066893645141198854487503147226318730158493210982567772716162869840L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let R2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                10548244869191429978994573331033429460802791853191679921432716242390096998215982561051229194803656270150791181542353263212179039510L,
                17623338845092751517427595119320347017334966146230013113905734683582704966390296970846105400364294574370981828797535336936167097772L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let Q3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                13106015910647201458426811493288965923311702902321179794984306791335898269651901670809619116119997952683697617529379507339288983622L,
                0L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let P3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                5822289030790821842647204127346110197186614331916510409554480418611145246532692679762948023941031185216358707524703325193156147113L,
                0L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let R3 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                19978714732817982296321998790126652405475699311529669091328949981490769847281914491438519436155586335833863255694913096932863948652L,
                14167827257511306746606440016400170231086622175754382579855491498256779752299521404090563911050166061448571907478184141518856743652L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );

        let pPoints = DoubledPointArray(P2, E6, e2);
        let qPoints = DoubledPointArray(Q2, E6, e2);
        let rPoints = DoubledPointArray(R2, E6, e2);

        let twoTorsions = [pPoints[e2 - 1], qPoints[e2 - 1], rPoints[e2 - 1]];
        let threePoints = [P3, Q3, R3];

        for (idxTwo in 0..2){
            for (idxThree in 0..2){
                TwoIsogenyOfPointTestHelper(Isogeny, twoTorsions[idxTwo], threePoints[idxThree], nQubits);
            }
        }
    }

    operation LargeIsogenyOfPointTest() : Unit {
        // Should take about 9 hours
        LargeIsogenyOfPointTestHelper(TwoIsogenyOfPoint);
    }

    /// The isogeny formula only computes an isogeny if
    /// the kernel point really has exact order 2. 
    /// Since it's difficult to produce points like this
    /// in Q#, this simply picks random points. 
    /// This will simply ensure that the arithmetic 
    /// matches the classical function.
    operation RandomIsogenyOfPointTestHelper (
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ,
            ECPointMontgomeryXZ
        ) => Unit is Ctl + Adj),
        nQubits : Int,
        nTests : Int
    ) : Unit {
        for (idxTest in 0.. nTests - 1){
            let modulus = RandomFp2Modulus(nQubits);
            let pxFp2 = RandomFp2ElementClassical(modulus);
            let pzFp2 = RandomFp2ElementClassical(modulus);
            let kernelPoint = ECPointMontgomeryXZClassical(pxFp2, pzFp2);
            let qxFp2 = RandomFp2ElementClassical(modulus);
            let qzFp2 = RandomFp2ElementClassical(modulus);
            let inputPoint = ECPointMontgomeryXZClassical(qxFp2, qzFp2);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
            TwoIsogenyOfPointTestHelper(Isogeny, kernelPoint, inputPoint, nQubits);
        }
    }


    operation RandomIsogenyOfPointTest() : Unit {
        let nQubits = 12;
        let nTests = 100;
        RandomIsogenyOfPointTestHelper(TwoIsogenyOfPoint, nQubits, nTests);
    }

    ///////////////// TWO ISOGENY OF A CURVE ///////////////// 
    ///
    /// # Summary
    /// Given a point P of exact order 2 in a qubit register, implicitly
    /// on an elliptic curve E, computes the curve isogenous
    /// to E via the isogeny with kernel <P>
    ///
    /// # Inputs
    /// ## point
    /// The point P
    /// ## outputCurve
    /// Blank qubit register to contain the output
    ///
    /// # Operations
    /// This can test:
    ///		* TwoIsogenyOfCurveMontgomeryXZ
    operation TwoIsogenyOfCurveTestHelper(
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECCoordsMontgomeryFormAPlusC
        ) => Unit is Ctl),
        kernelPoint : ECPointMontgomeryXZClassical,
        nQubits : Int
    ) : Unit {
        body (...){
            // Bookkeeping and qubit allocation
            using (register = Qubit[8 * nQubits]) {
                mutable actualCoefficient = 0L;
                let modulus = kernelPoint::x::modulus;
                let zeroPoint = ECPointMontgomeryXZClassical(
                    Fp2ElementClassical(modulus, 0L,0L),
                    Fp2ElementClassical(modulus, 0L,0L)
                );
                let zeroCurve = ECCoordsMontgomeryFormAPlusCClassical(
                    Fp2ElementClassical(modulus, 0L,0L),
                    Fp2ElementClassical(modulus, 0L,0L)
                );
                mutable actualKernelPoint = zeroPoint;
                mutable resultCurve = zeroCurve;

                // Write to qubit registers
                mutable qKernelPoint = CreateECPointMontgomeryXZ(kernelPoint, register[0..4 * nQubits - 1]);
                mutable qCurve = CreateECCoordsMontgomeryFormAPlusC(zeroCurve, register[4 * nQubits .. 8 * nQubits - 1]);

                // Run test
                Isogeny(qKernelPoint, qCurve);
 
                // Compute expected classical result
                let imageCurve = TwoIsogenousCurveMontgomeryXZClassical(kernelPoint);

                // Check results
                set actualKernelPoint = MeasureECPointMontgomeryXZ(qKernelPoint);
                set resultCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                Fact(
                    IsEqualMontgomeryXZClassical(kernelPoint, actualKernelPoint), 
                    $"Kernel point : Expected ({kernelPoint::x::real} + {kernelPoint::x::imag}i,{kernelPoint::z::real} + {kernelPoint::z::imag}i)
                    , got ({actualKernelPoint::x::real} + {actualKernelPoint::x::imag}i,{actualKernelPoint::z::real} + {actualKernelPoint::z::imag}i)"
                );
                Fact(IsEqualFp2Element(imageCurve::a24Plus, resultCurve::a24Plus)
                            and IsEqualFp2Element(imageCurve::c24, resultCurve::c24), 
                            $"Isogenous curve : Expected {imageCurve}, got {resultCurve}");
                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(kernelPoint, qKernelPoint);

                        // controls are |0>, no addition is computed
                        // Run test
                        (Controlled Isogeny) (controls, (qKernelPoint, qCurve));

                        // Check results
                        set actualKernelPoint = MeasureECPointMontgomeryXZ(qKernelPoint);
                        set resultCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(
                            IsEqualMontgomeryXZClassical(kernelPoint, actualKernelPoint), 
                            $"Control 0: Kernel point : Expected ({kernelPoint::x::real} + {kernelPoint::x::imag}i,{kernelPoint::z::real} + {kernelPoint::z::imag}i)
                            , got ({actualKernelPoint::x::real} + {actualKernelPoint::x::imag}i,{actualKernelPoint::z::real} + {actualKernelPoint::z::imag}i)"
                        );
                        Fact(IsEqualFp2Element(zeroCurve::a24Plus, resultCurve::a24Plus)
                                    and IsEqualFp2Element(zeroCurve::c24, resultCurve::c24), 
                                    $"Control 0: Isogenous curve : Expected {zeroCurve}, got {resultCurve}");

                        // Write to qubit registers
                        EncodeECPointMontgomeryXZ(kernelPoint, qKernelPoint);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                         (Controlled Isogeny) (controls, (qKernelPoint, qCurve));

                        // Check results
                        set actualKernelPoint = MeasureECPointMontgomeryXZ(qKernelPoint);
                        set resultCurve = MeasureECCoordsMontgomeryFormAPlusC(qCurve);
                        Fact(
                            IsEqualMontgomeryXZClassical(kernelPoint, actualKernelPoint), 
                            $"Control 1: Kernel point : Expected ({kernelPoint::x::real} + {kernelPoint::x::imag}i,{kernelPoint::z::real} + {kernelPoint::z::imag}i)
                            , got ({actualKernelPoint::x::real} + {actualKernelPoint::x::imag}i,{actualKernelPoint::z::real} + {actualKernelPoint::z::imag}i)"
                        );
                        Fact(IsEqualFp2Element(imageCurve::a24Plus, resultCurve::a24Plus)
                                    and IsEqualFp2Element(imageCurve::c24, resultCurve::c24), 
                                    $"Control 1: Isogenous curve : Expected {imageCurve}, got {resultCurve}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation SmallIsogenyOfCurveTestHelper(
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECCoordsMontgomeryFormAPlusC
        ) => Unit is Ctl)
    ):Unit {
        let nQubits = 10;
        let p = 863L;
        let e2=5;
        let E0=ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(p, 8L,0L),
            Fp2ElementClassical(p, 4L,0L)		
        );
        let Q2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 472L,767L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let P2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 399L,796L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let R2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 679L, 665L),
            Fp2ElementClassical(p, 1L,0L)
        );
        let zeroPoint = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(p, 0L,0L),
            Fp2ElementClassical(p, 0L,0L)
        );

        let pPoints = DoubledPointArray(P2, E0, e2);
        let qPoints = DoubledPointArray(Q2, E0, e2);
        let rPoints = DoubledPointArray(R2, E0, e2);

        let twoTorsions = [pPoints[e2 - 1], qPoints[e2 - 1], rPoints[e2 - 1]];

        for (idxTwo in 0..2){
            TwoIsogenyOfCurveTestHelper(Isogeny, twoTorsions[idxTwo], nQubits);
        }
    }

    operation SmallIsogenyOfCurveTest() : Unit {
        SmallIsogenyOfCurveTestHelper(TwoIsogenyOfCurveMontgomeryXZ);
    }

    operation LargeIsogenyOfCurveTestHelper(
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECCoordsMontgomeryFormAPlusC
        ) => Unit is Ctl)
    ):Unit {
        //SIKE - 434 parameters
        let nQubits = 434;
        let e2 = 216;
        let modulus = 24439423661345221551909145011457493619085780243761596511325807336205221239331976725970216671828618445898719026692884939342314733567L;
        let E6 = ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(modulus, 6L, 0L),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let Q2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                8633131302536015373065425580178973814526244742660764898957635611033517358603093513483897324469034427019598357249425684820405193836L,
                1640555213321637736080614728970921962714590288563692816952785470842808462670732196555713644986698688787353020078064569199240185333L
              ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let P2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                2634539327592482918121599540115765431217195093350648632832477775508933673747596362667240890051240463853167541162279343167040310088L,
                18590308952679468489364793668589003541299106140709579196186461020066893645141198854487503147226318730158493210982567772716162869840L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );
        let R2 = ECPointMontgomeryXZClassical(
            Fp2ElementClassical(modulus,
                10548244869191429978994573331033429460802791853191679921432716242390096998215982561051229194803656270150791181542353263212179039510L,
                17623338845092751517427595119320347017334966146230013113905734683582704966390296970846105400364294574370981828797535336936167097772L
            ),
            Fp2ElementClassical(modulus, 1L, 0L)
        );

        let pPoints = DoubledPointArray(P2, E6, e2);
        let qPoints = DoubledPointArray(Q2, E6, e2);
        let rPoints = DoubledPointArray(R2, E6, e2);

        let twoTorsions = [pPoints[e2 - 1], qPoints[e2 - 1], rPoints[e2 - 1]];

        for (idxTwo in 0..2){
            TwoIsogenyOfCurveTestHelper(Isogeny, twoTorsions[idxTwo], nQubits);
        }
    }

    operation LargeIsogenyOfCurveTest() : Unit {
        // Under 1 hour
        LargeIsogenyOfCurveTestHelper(TwoIsogenyOfCurveMontgomeryXZ);
    }

    /// The isogeny formula only computes an isogeny if
    /// the kernel point really has exact order 2. 
    /// Since it's difficult to produce points like this
    /// in Q#, this simply picks random points. 
    /// This will simply ensure that the arithmetic 
    /// matches the classical function.
    operation RandomIsogenyOfCurveTestHelper (
        Isogeny : ((
            ECPointMontgomeryXZ,
            ECCoordsMontgomeryFormAPlusC
        ) => Unit is Ctl),
        nQubits : Int,
        nTests : Int
    ) : Unit {
        for (idxTest in 0.. nTests - 1){
            let modulus = RandomFp2Modulus(nQubits);
            let pxFp2 = RandomFp2ElementClassical(modulus);
            let pzFp2 = RandomFp2ElementClassical(modulus);
            let kernelPoint = ECPointMontgomeryXZClassical(pxFp2, pzFp2);
            let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
            TwoIsogenyOfCurveTestHelper(Isogeny, kernelPoint, nQubits);
        }
    }


    operation RandomIsogenyOfCurveTest() : Unit {
        let nQubits = 12;
        let nTests = 100;
        RandomIsogenyOfCurveTestHelper(TwoIsogenyOfCurveMontgomeryXZ, nQubits, nTests);
    }


    ///////////////// SIKE ISOGENY ///////////////// 
    ///
    /// # Summary
    ///
    /// # Operations
    /// This can test:
    ///		* 
    operation SIKEIsogenyTestHelper(
        SIKEIsogeny : ((
            ECCoordsMontgomeryFormAPlusCClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            Int,
            LittleEndian,
            Fp2MontModInt
        ) => Unit is Ctl),
        curve : ECCoordsMontgomeryFormAPlusCClassical,
        pointP : ECPointMontgomeryXZClassical,
        pointQ : ECPointMontgomeryXZClassical,
        pointR : ECPointMontgomeryXZClassical,
        height : Int,
        coefficient : BigInt,
        nQubits : Int
    ) : Unit {
        body (...){
            // Bookkeeping and qubit allocation
            using (register = Qubit[height + 2 * nQubits]) {
                mutable actualCoefficient = 0L;
                let modulus = pointP::x::modulus;
                let zeroFp2 = Fp2ElementClassical(modulus, 0L, 0L);
                let zeroPoint = ECPointMontgomeryXZClassical(zeroFp2, zeroFp2);
                let zeroCurve = ECCoordsMontgomeryFormAPlusCClassical(zeroFp2, zeroFp2);
                mutable actualJInvariant = zeroFp2;
                let qCoefficient = LittleEndian(register[2 * nQubits .. 2 * nQubits + height - 1]);
                let qJInvariant = QubitArrayAsFp2MontModInt(modulus, register[0..2 * nQubits - 1]);


                // Write to qubit registers
                ApplyXorInPlaceL(coefficient, qCoefficient);


                // Run test
                SIKEIsogeny(curve, pointP, pointQ, pointR, height, qCoefficient, qJInvariant);
 
                // Compute expected classical result
                let trueJInvariant = SIKETwoIsogenyClassical(curve, pointP, pointQ, pointR, height, coefficient);

                // Check results
                set actualJInvariant = MeasureFp2MontModInt(qJInvariant);
                set actualCoefficient = MeasureBigInteger(qCoefficient);
                Fact(
                    IsEqualFp2Element(actualJInvariant, trueJInvariant), 
                    $"J-invariant : Expected ({trueJInvariant::real} + {trueJInvariant::imag}i), got ({actualJInvariant::real} + {actualJInvariant::imag}i)"
                );
                Fact(actualCoefficient == coefficient, $"Coefficient: Expected {coefficient}, got {actualCoefficient}");
                for (numberOfControls in 1..2) { 
                    using (controls = Qubit[numberOfControls]) {
                        // Write to qubit registers
                        ApplyXorInPlaceL(coefficient, qCoefficient);

                        // Run test
                        (Controlled SIKEIsogeny) (controls, (curve, pointP, pointQ, pointR, height, qCoefficient, qJInvariant));

                        // Check results
                        set actualJInvariant = MeasureFp2MontModInt(qJInvariant);
                        set actualCoefficient = MeasureBigInteger(qCoefficient);
                        Fact(
                            IsEqualFp2Element(actualJInvariant, zeroFp2), 
                            $"Control 0: J-invariant : Expected ({zeroFp2::real} + {zeroFp2::imag}i), got ({actualJInvariant::real} + {actualJInvariant::imag}i)"
                        );
                        Fact(actualCoefficient == coefficient, $"Control 0: Coefficient: Expected {coefficient}, got {actualCoefficient}");

                        // Write to qubit registers
                        ApplyXorInPlaceL(coefficient, qCoefficient);

                        // Flip controls
                        ApplyToEach(X, controls);

                        // Run test
                         (Controlled SIKEIsogeny) (controls, (curve, pointP, pointQ, pointR, height, qCoefficient, qJInvariant));

                        // Check results
                        set actualJInvariant = MeasureFp2MontModInt(qJInvariant);
                        set actualCoefficient = MeasureBigInteger(qCoefficient);
                        Fact(
                            IsEqualFp2Element(actualJInvariant, trueJInvariant), 
                            $"Control 1: J-invariant : Expected ({trueJInvariant::real} + {trueJInvariant::imag}i), got ({actualJInvariant::real} + {actualJInvariant::imag}i)"
                        );
                        Fact(actualCoefficient == coefficient, $"Control 1: Coefficient: Expected {coefficient}, got {actualCoefficient}");

                        ResetAll(controls);
                    }
                }
            }
        }
    }

    operation RandomSIKEIsogenyTestHelper(
        SIKEIsogeny : ((
            ECCoordsMontgomeryFormAPlusCClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            ECPointMontgomeryXZClassical,
            Int,
            LittleEndian,
            Fp2MontModInt
        ) => Unit is Ctl),
        twoTorsion : Int, 
        nTests : Int
    ) : Unit {
        let SIKEps = GetSIKEParams(twoTorsion);
        let nQubits = BitSizeL(SIKEps::prime);
        let curve = ECCoordsMontgomeryFormAPlusCClassical(
            Fp2ElementClassical(SIKEps::prime, 8L, 0L),
            Fp2ElementClassical(SIKEps::prime, 4L, 0L)
        );
        for (idxTest in 0..nTests - 1){

            let coefficient = RandomBigInt(2L ^ SIKEps::twoOrder);
            SIKEIsogenyTestHelper(
                SIKEIsogeny,
                curve,
                SIKEps::pointP,
                SIKEps::pointQ,
                SIKEps::pointR,
                SIKEps::twoOrder,
                coefficient,
                nQubits
            );
        }
    }

    operation RandomSIKEIsogenyTest () : Unit {
        let twoTorsion = 8;
        let nTests = 100;
        RandomSIKEIsogenyTestHelper(ComputeSIKETwoIsogeny, twoTorsion, nTests);
    }

    operation InreasingSIKEIsogenyTest () : Unit {
        for (twoTorsion in 13.. 128){
            Message($"============================================================
            
          TESTING TWO TORSION OF {twoTorsion}
            
============================================================");
            RandomSIKEIsogenyTestHelper(ComputeSIKETwoIsogeny, twoTorsion, 1);
        }
    }

}
