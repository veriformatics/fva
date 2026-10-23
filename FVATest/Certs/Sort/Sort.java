import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class Sort {
    public static void main(String[] args) throws Exception {
        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        List<Long> xs = new ArrayList<>();
        for (String line; (line = in.readLine()) != null; ) {
            if (!line.isEmpty()) xs.add(Long.parseLong(line));
        }
        Collections.sort(xs);
        StringBuilder out = new StringBuilder();
        for (long x : xs) out.append(x).append('\n');
        System.out.print(out);
    }
}
