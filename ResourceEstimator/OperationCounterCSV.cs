// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

// Library that deals with making human-friendly the CSV tracer's output
namespace CommaSeparated
{
    using FileHelpers; // csv parsing

    [DelimitedRecord("\t")]
    [IgnoreFirst(1)]
    public class OperationCounterCSV
    {
        public string Name
        { get; set; }

        public string Variant
        { get; set; }

        public string Caller
        { get; set; }

        public string CallerVariant
        { get; set; }

        public long Count
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal CNOTAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal CNOTSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal CNOTVariance
        { get; set; }

        public long CNOTSum
        { get; set; }

        public long CNOTMin
        { get; set; }

        public long CNOTMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal QubitCliffordAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal QubitCliffordSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal QubitCliffordVariance
        { get; set; }

        public long QubitCliffordSum
        { get; set; }

        public long QubitCliffordMin
        { get; set; }

        public long QubitCliffordMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal RAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal RSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal RVariance
        { get; set; }

        public long RSum
        { get; set; }

        public long RMin
        { get; set; }

        public long RMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal MeasureAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal MeasureSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal MeasureVariance
        { get; set; }

        public long MeasureSum
        { get; set; }

        public long MeasureMin
        { get; set; }

        public long MeasureMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal TAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal TSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal TVariance
        { get; set; }

        public long TSum
        { get; set; }

        public long TMin
        { get; set; }

        public long TMax
        { get; set; }
    }
}