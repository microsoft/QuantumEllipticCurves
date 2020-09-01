// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

// Library that deals with making human-friendly the CSV tracer's output
namespace CommaSeparated
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
        public decimal StartTimeAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal StartTimeSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))] // [FieldConverter(ConverterKind.Decimal, ".")]
        public decimal? StartTimeVariance
        { get; set; }

        public long StartTimeSum
        { get; set; }

        public long StartTimeMin
        { get; set; }

        public long StartTimeMax
        { get; set; }
    }
}