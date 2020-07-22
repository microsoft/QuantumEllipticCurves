using System;
using System.Collections.Generic;
using Microsoft.Quantum.Simulation.Simulators.QCTraceSimulators;

using FileHelpers; // csv parsing
using System.Globalization;

// Library that deals with making human-friendly the CSV tracer's output

namespace cs
{
    [DelimitedRecord("\t")]
    [IgnoreFirst(1)]
    public class DepthCounterCSV
    {
        public string Name;
        public string Variant;
        public string Caller;
        public string CallerVariant;
        public long Count;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal DepthAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal DepthSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal? DepthVariance;
        public long DepthSum;
        public long DepthMin;
        public long DepthMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal StartTimeAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal StartTimeSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))] // [FieldConverter(ConverterKind.Decimal, ".")]
        public decimal? StartTimeVariance;
        public long StartTimeSum;
        public long StartTimeMin;
        public long StartTimeMax;
    }

    [DelimitedRecord("\t")]
    [IgnoreFirst(1)]
    public class WidthCounterCSV
    {
        public string Name;
        public string Variant;
        public string Caller;
        public string CallerVariant;
        public long Count;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal InputWidthAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal InputWidthSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal InputWidthVariance;
        public long InputWidthSum;
        public long InputWidthMin;
        public long InputWidthMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ExtraWidthAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ExtraWidthSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ExtraWidthVariance;
        public long ExtraWidthSum;
        public long ExtraWidthMin;
        public long ExtraWidthMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ReturnWidthAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ReturnWidthSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal ReturnWidthVariance;
        public long ReturnWidthSum;
        public long ReturnWidthMin;
        public long ReturnWidthMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal BorrowedWidthAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal BorrowedWidthSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal BorrowedWidthVariance;
        public long BorrowedWidthSum;
        public long BorrowedWidthMin;
        public long BorrowedWidthMax;
    }

    [DelimitedRecord("\t")]
    [IgnoreFirst(1)]
    public class OperationCounterCSV
    {
        public string Name;
        public string Variant;
        public string Caller;
        public string CallerVariant;
        public long Count;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal CNOTAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal CNOTSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal CNOTVariance;
        public long CNOTSum;
        public long CNOTMin;
        public long CNOTMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal QubitCliffordAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal QubitCliffordSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal QubitCliffordVariance;
        public long QubitCliffordSum;
        public long QubitCliffordMin;
        public long QubitCliffordMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal RAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal RSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal RVariance;
        public long RSum;
        public long RMin;
        public long RMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal MeasureAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal MeasureSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal MeasureVariance;
        public long MeasureSum;
        public long MeasureMin;
        public long MeasureMax;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal TAverage;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal TSecondMoment;
        [FieldConverter(typeof(QDecimalConverter))]
        public decimal TVariance;
        public long TSum;
        public long TMin;
        public long TMax;
}

    public class QDecimalConverter : ConverterBase
    {
        public override object StringToField(string from)
        {
            if (from == "NaN")
            {
                return Convert.ToDecimal(-1);
            }
            else
            {
                return Decimal.Parse(from, NumberStyles.AllowExponent | NumberStyles.AllowDecimalPoint);
            }
        }
        public override string FieldToString(object fieldValue)
        {
            if (Convert.ToDecimal(fieldValue) == Convert.ToDecimal(-1))
            {
                return "NaN";
            }
            else
            {
                return ((decimal)fieldValue).ToString();
            }
        }
    }
    class DisplayCSV
    {
        public static void Depth(string csv, string line_name, bool all = false)
        {
            var engine = new FileHelperAsyncEngine<DepthCounterCSV>();
            using (engine.BeginReadString(csv))
            {
                // This wont display anything, we have dropped it
                foreach (var err in engine.ErrorManager.Errors)
                {
                    Console.WriteLine();
                    Console.WriteLine("Error on Line number: {0}", err.LineNumber);
                    Console.WriteLine("Record causing the problem: {0}", err.RecordString);
                    Console.WriteLine("Complete exception information: {0}", err.ExceptionInfo.ToString());
                }

                // The engine is IEnumerable
                foreach (DepthCounterCSV cust in engine)
                {
                    // your code here
                    if (cust.Name == line_name || all)
                    {
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") depth avg " + cust.DepthAverage + " (variance " + cust.DepthVariance + ")");
                    }
                }
            }
        }

        public static void Width(string csv, string line_name, bool all = false)
        {
            var engine = new FileHelperAsyncEngine<WidthCounterCSV>();
            using (engine.BeginReadString(csv))
            {
                // This wont display anything, we have dropped it
                foreach (var err in engine.ErrorManager.Errors)
                {
                    Console.WriteLine();
                    Console.WriteLine("Error on Line number: {0}", err.LineNumber);
                    Console.WriteLine("Record causing the problem: {0}", err.RecordString);
                    Console.WriteLine("Complete exception information: {0}", err.ExceptionInfo.ToString());
                }

                // The engine is IEnumerable
                foreach (WidthCounterCSV cust in engine)
                {
                    // your code here
                    if (cust.Name == line_name || all)
                    {
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") initial width avg " + cust.InputWidthAverage + " (variance " + cust.InputWidthVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") extra width avg " + cust.ExtraWidthAverage + " (variance " + cust.ExtraWidthVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") return width avg " + cust.ReturnWidthAverage + " (variance " + cust.ReturnWidthVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") borrowed width avg " + cust.BorrowedWidthAverage + " (variance " + cust.BorrowedWidthVariance + ")");
                    }
                }
            }
        }

        public static void Operations(string csv, string line_name, bool all = false)
        {
            var engine = new FileHelperAsyncEngine<OperationCounterCSV>();
            using (engine.BeginReadString(csv))
            {
                // This wont display anything, we have dropped it
                foreach (var err in engine.ErrorManager.Errors)
                {
                    Console.WriteLine();
                    Console.WriteLine("Error on Line number: {0}", err.LineNumber);
                    Console.WriteLine("Record causing the problem: {0}", err.RecordString);
                    Console.WriteLine("Complete exception information: {0}", err.ExceptionInfo.ToString());
                }

                // The engine is IEnumerable
                foreach (OperationCounterCSV cust in engine)
                {
                    // your code here
                    if (cust.Name == line_name || all)
                    {
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") CNOT count avg " + cust.CNOTAverage + " (variance " + cust.CNOTVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") Clifford count avg " + cust.QubitCliffordAverage + " (variance " + cust.QubitCliffordVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") T count avg " + cust.TAverage + " (variance " + cust.TVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") R count avg " + cust.RAverage + " (variance " + cust.RVariance + ")");
                        Console.WriteLine(cust.Name + " (<- " + cust.Caller + ") Measure count avg " + cust.MeasureAverage + " (variance " + cust.MeasureVariance + ")");
                    }
                }
            }
        }

        public static void All(Dictionary<String, String> csv, string line_name, bool all = false)
        {
            // print results
            Depth(csv[MetricsCountersNames.depthCounter], line_name, all);
            Console.WriteLine();
            Width(csv[MetricsCountersNames.widthCounter], line_name, all);
            Console.WriteLine();
            Operations(csv[MetricsCountersNames.primitiveOperationsCounter], line_name, all);
            Console.WriteLine();
        }

         public static string CSV(Dictionary<String, String> csv, string line_name, bool display_header = false, string comment = "", bool all = false, string suffix = "")
        {
            string results = "";
            // print results
            if (display_header)
            {
                results += "operation, CNOT count, 1-qubit Clifford count, T count, R count, M count, T depth, initial width, extra width, comment, \n";
            }
            results += $"{Environment.NewLine}{line_name}{suffix}, ";
            var countEngine = new FileHelperAsyncEngine<OperationCounterCSV>();
            using (countEngine.BeginReadString(csv[MetricsCountersNames.primitiveOperationsCounter]))
            {
                // The engine is IEnumerable
                foreach (OperationCounterCSV cust in countEngine)
                {
                    if (cust.Name == line_name || all)
                    {
                        results += $"{cust.CNOTAverage}, {cust.QubitCliffordAverage}, {cust.TAverage}, {cust.RAverage}, {cust.MeasureAverage}, ";
                    }
                }
            }
            var depthEngine = new FileHelperAsyncEngine<DepthCounterCSV>();
            using (depthEngine.BeginReadString(csv[MetricsCountersNames.depthCounter]))
            {
                // The engine is IEnumerable
                foreach (DepthCounterCSV cust in depthEngine)
                {
                    if (cust.Name == line_name || all)
                    {
                        results += $"{cust.DepthAverage}, ";
                    }
                }
            }
            var widthEngine = new FileHelperAsyncEngine<WidthCounterCSV>();
            using (widthEngine.BeginReadString(csv[MetricsCountersNames.widthCounter]))
            {
                // The engine is IEnumerable
                foreach (WidthCounterCSV cust in widthEngine)
                {
                    if (cust.Name == line_name || all)
                    {
                        results +=$"{cust.InputWidthAverage}, {cust.ExtraWidthAverage}, ";
                    }
                }
            }
            results += $"{comment}, ";
            return results;
        }
    }
}