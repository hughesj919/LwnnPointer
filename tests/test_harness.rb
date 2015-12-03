puts "Running ..."

content = open(ARGV[0]).read

bin = content.lines.select { |y| y !~ /\[.*/ }.map do |x|
  x.split(":")[1].strip.to_i
end

expected = [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 1, 1, 1, 1]

results = []
bin.each_with_index do |c, i|
  results << (c == expected[i])
  puts "#{c}, #{expected[i]}"
end

if results.all? { |r| r == true }
  puts "Matches the output of the official version."
else
  puts "Output does not match."
end
