namespace CommaSeparated
{
    using System;
    using System.Collections.Generic;
    using System.Globalization;
    using FileHelpers;

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
                return decimal.Parse(from, NumberStyles.AllowExponent | NumberStyles.AllowDecimalPoint);
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
}