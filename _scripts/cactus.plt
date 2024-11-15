# A cactus plot generator that was produced by ChatGPT
# (with a little bit of help by Igor)

# Set the output format to PNG (or whatever you prefer)
set terminal pngcairo size 800,600 enhanced font 'Verdana,14'
set output output_name

# Title and labels
set title "Cactus Plot"
set xlabel "Number of instances solved"
set ylabel "Time (seconds)"

# Grid and style
set grid
set style data linespoints

# Set the data separator (if CSV, usually comma, but in this case no separator is needed since it's just one column)
set datafile separator ','

# change the lines and markers
set style line 1 lt 1 pt 7 ps 1.5 lc rgb "orange"

# Sort the data first and then use cumulative numbering for solved instances
plot input_name using ($0):($1+1) with linespoints linestyle 1 title "Time per instance"
