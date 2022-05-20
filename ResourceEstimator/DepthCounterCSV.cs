// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

// Library that deals with making human-friendly the CSV tracer's output
namespace Microsoft.Quantum.Crypto.ResourceEstimator.CommaSeparated
{
    using FileHelpers; // csv parsing

    [DelimitedRecord("\t")]
    [IgnoreFirst(1)]
    public class DepthCounterCSV
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
        public decimal DepthAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal DepthSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal? DepthVariance
        { get; set; }

        public long DepthSum
        { get; set; }

        public long DepthMin
        { get; set; }

        public long DepthMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal StartTimeDifferenceAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal StartTimeDifferenceSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))] // [FieldConverter(ConverterKind.Decimal, ".")]
        public decimal? StartTimeDifferenceVariance
        { get; set; }

        public long StartTimeDifferenceSum
        { get; set; }

        public long StartTimeDifferenceMin
        { get; set; }

        public long StartTimeDifferenceMax
        { get; set; }

         [FieldConverter(typeof(QDecimalConverter))]
        public decimal WidthAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal WidthSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal? WidthVariance
        { get; set; }

        public long WidthSum
        { get; set; }

        public long WidthMin
        { get; set; }

        public long WidthMax
        { get; set; }
    }
}