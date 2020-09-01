// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

namespace Microsoft.Quantum.ModularArithmetic.DebugHelpers 
{
    open Microsoft.Quantum.Intrinsic;
    open Microsoft.Quantum.Crypto.Basics;
    open Microsoft.Quantum.Crypto.Arithmetic;
    open Microsoft.Quantum.Crypto.ModularArithmetic;
    open Microsoft.Quantum.Crypto.EllipticCurves;
    open Microsoft.Quantum.Crypto.Fp2Arithmetic;
    open Microsoft.Quantum.Crypto.Isogenies;
    open Microsoft.Quantum.Arithmetic;
    open Microsoft.Quantum.Canon;
    open Microsoft.Quantum.Convert;
    open Microsoft.Quantum.Math;
    open Microsoft.Quantum.Diagnostics;



    operation DumpLittleEndian(xs : LittleEndian, message : String) : Unit{
        body(...){
            let result = MeasureBigInteger(xs);
            Message($"{message}{result}");
            ApplyXorInPlaceL(result,xs);
        }
        adjoint(...){
            DumpLittleEndian(xs,message);
        }
        controlled(controls,...){
            DumpLittleEndian(xs, message);
        }
        controlled adjoint(controls,...){
            DumpLittleEndian(xs, message);
        }
    }



    operation BitDump(qubit:Qubit,message:String):Unit{
        body(...){
            Message(message + $"{M(qubit)}");
        }
        adjoint(...){
            Message(message + $"{M(qubit)}");
        }
        controlled(controls,...){
            Message(message + $"{M(qubit)}");
        }
        controlled adjoint(controls,...){
            Message(message + $"{M(qubit)}");
        }
    }


    operation DumpECPointMontgomery(point : ECPointMontgomeryForm, message : String) : Unit {
        body (...){
            let x = MeasureMontgomeryInteger(point::xs);
            let y = MeasureMontgomeryInteger(point::ys);
            Message(message + $"({x}, {y})");
            EncodeBigIntInMontgomeryForm(x, point::xs);
            EncodeBigIntInMontgomeryForm(y, point::ys);
        }
        controlled (controls, ...){
            DumpECPointMontgomery(point, message);
        }
        adjoint controlled (controls, ...){
            DumpECPointMontgomery(point, message);
        }
        adjoint (...){
            DumpECPointMontgomery(point, message);
        }
    }


    operation DumpFp2(element : Fp2MontModInt, message : String) :Unit {
        body (...){
            let elementC = MeasureFp2MontModInt(element);
            Message(message + $"{elementC::real}+{elementC::imag}i");
            EncodeFp2MontModInt(elementC, element);
        }
        controlled (controls, ... ){
            DumpFp2(element, message);
        }
        controlled adjoint (controls, ...){
            DumpFp2(element, message);
        }
        adjoint (...){
            DumpFp2(element, message);
        }
    }

 
    function ECPointMontgomeryXZClassicalAsString(point : ECPointMontgomeryXZClassical) : String {
        return $"({point::x::real}+{point::x::imag}i,{point::z::real}+{point::z::imag}i)";
    }


    function PrintClassicalECPointArray(points: ECPointMontgomeryXZClassical[] ) : Unit {
        for (idx in 0..Length(points) - 1){
            Message($"Point {idx}:" + ECPointMontgomeryXZClassicalAsString(points[idx]));
        }
    }


    operation DumpECPointArray(points : ECPointMontgomeryXZ[], message : String) : Unit {
        body (...){
            Message(message);
            for (idx in 0.. Length(points) - 1){
                DumpECPoint(points[idx], $"Point {idx}:");
            }
        }
        controlled (controls, ...){
            DumpECPointArray(points, message);
        }
        adjoint controlled (controls, ...){
            DumpECPointArray(points, message);
        }
        adjoint (...){
            DumpECPointArray(points, message);
        }
    }


    function OutputECPoint(point:ECPointClassical):Unit {
        Message($"Point: ({point::x},{point::y},{point::z})");
    }


    operation DumpECPoint(point : ECPointMontgomeryXZ, message : String) : Unit {
        body (...) {
            let pointC = MeasureECPointMontgomeryXZ(point);
            Message(message + ECPointMontgomeryXZClassicalAsString(pointC));
            EncodeECPointMontgomeryXZ(pointC, point);
        }
        controlled (controls, ... ){
            DumpECPoint(point, message);
        }
        controlled adjoint (controls, ... ){
            DumpECPoint(point, message);
        }
        adjoint (... ){
            DumpECPoint(point, message);
        }
    }


    operation DumpECCurve(curve : ECCoordsMontgomeryFormAPlusC, message : String) : Unit {
        body (...) {
            let curveC = MeasureECCoordsMontgomeryFormAPlusC(curve);
            Message(message + $"({curveC::a24Plus::real}+{curveC::a24Plus::imag}i,{curveC::c24::real}+{curveC::c24::imag}i)");
            EncodeECCoordsMontgomeryFormAPlusC(curveC, curve);
        }
        controlled (controls, ... ){
            DumpECCurve(curve, message);
        }
        controlled adjoint (controls, ... ){
            DumpECCurve(curve, message);
        }
        adjoint (... ){
            DumpECCurve(curve, message);
        }
    }
    

    operation DumpJInvariant(curve : ECCoordsMontgomeryFormAPlusC, message : String) : Unit {
        body (...) {
            let curveC = MeasureECCoordsMontgomeryFormAPlusC(curve);
            let j = JInvariantClassical(MontgomeryCurveClassicalAsACFromAPlusC(curveC));
            Message(message + $"({j::real}+{j::imag}i)");
            EncodeECCoordsMontgomeryFormAPlusC(curveC, curve);
        }
        controlled (controls, ... ){
            DumpJInvariant(curve, message);
        }
        controlled adjoint (controls, ... ){
            DumpJInvariant(curve, message);
        }
        adjoint (... ){
            DumpJInvariant(curve, message);
        }
    }


    operation DumpQubits(qubits:Qubit[],message:String):Unit {
        body(...){
            mutable newmessage = message;
            for (idx in 0..Length(qubits)-1){
                if (ResultAsBool(M(qubits[idx]))){
                    set newmessage = newmessage + "1";
                } else {
                    set newmessage = newmessage+"0";
                }
            }
            Message(newmessage);
        }
        adjoint(...){
            DumpQubits(qubits, message);
        }
        controlled(controls,...){
            DumpQubits(qubits, message);
        }
        controlled adjoint(controls,...){
            DumpQubits(qubits, message);
        }
    }

}