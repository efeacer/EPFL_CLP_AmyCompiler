object BodyMassIndexCalculator {
    def calculateBMI(height: Int, weight: Int): Int = {
        (weight * 10000) / (height * height)
    }

    def categorize(bodyMassIndex: Int): Int = {
        if (bodyMassIndex < 18) { 1 }
        else {
            if (bodyMassIndex < 25) { 2 }
            else {
                if (bodyMassIndex < 30) { 3 }
                else { 4 }
            }
        }
    }

    def printResult(height: Int, weight: Int): Unit = {
        val bodyMassIndex: Int = calculateBMI(height, weight);
        val category: Int = categorize(bodyMassIndex);
        Std.printString("Result for the adult person: ");
        Std.printString("Height: " ++ Std.intToString(height));
        Std.printString("Weight: " ++ Std.intToString(weight));
        Std.printString("Body Mass Index: " ++ Std.intToString(bodyMassIndex));
        category match {
            case 1 => Std.printString("Result: Underweight")
            case 2 => Std.printString("Result: Normal weight")
            case 3 => Std.printString("Result: Overweight")
            case 4 => Std.printString("Result: Obesity")
        }
    }

    Std.printString("This program performs the Body Mass Index Test for an adult. (meaningful values are expected)");
    Std.printString("Enter height (in cm): ");
    val height: Int = Std.readInt();
    Std.printString("Enter weight (in kg): ");
    val weight: Int = Std.readInt();
    printResult(height, weight)
}
