// Copyright (c) Microsoft Corporation.
// Licensed under the MIT license.

// Library that deals with making human-friendly the CSV tracer's output
namespace CommaSeparated
{
    using FileHelpers; // csv parsing

    [DelimitedRecord("\t")]
    [IgnoreFirst(1)]
    public class WidthCounterCSV
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
        public decimal InputWidthAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal InputWidthSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal InputWidthVariance
        { get; set; }

        public long InputWidthSum
        { get; set; }

        public long InputWidthMin
        { get; set; }

        public long InputWidthMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ExtraWidthAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ExtraWidthSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ExtraWidthVariance
        { get; set; }

        public long ExtraWidthSum
        { get; set; }

        public long ExtraWidthMin
        { get; set; }

        public long ExtraWidthMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ReturnWidthAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ReturnWidthSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ReturnWidthVariance
        { get; set; }

        public long ReturnWidthSum
        { get; set; }

        public long ReturnWidthMin
        { get; set; }

        public long ReturnWidthMax
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal BorrowedWidthAverage
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal BorrowedWidthSecondMoment
        { get; set; }

        [FieldConverter(typeof(QDecimalConverter))]
        public decimal BorrowedWidthVariance
        { get; set; }

        public long BorrowedWidthSum
        { get; set; }

        public long BorrowedWidthMin
        { get; set; }

        public long BorrowedWidthMax
        { get; set; }
    }
}