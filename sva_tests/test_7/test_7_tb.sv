module tb_assoc_array;

    // Associative array with a typed index (int)
    typedef string data_t;
    typedef int key_t;
    data_t data_by_key[key_t];

    // Task to add elements to the array
    task add_data(key_t key, data_t value);
        data_by_key[key] = value;
    endtask

    // Task to retrieve data from the array
    function data_t get_data(key_t key);
        if (data_by_key.exists(key))
            return data_by_key[key];
        else
            return "Key not found";
    endfunction

    //Unit test to verify associative array functionality
    initial begin
        // Add data to associative array
        add_data(1, "First Entry");
        add_data(2, "Second Entry");
        add_data(3, "Third Entry");

        // Retrieve and check data from the associative array
        assert(get_data(1) == "First Entry") else $error("Test failed: Expected 'First Entry'");
        assert(get_data(2) == "Second Entry") else $error("Test failed: Expected 'Second Entry'");
        assert(get_data(3) == "Third Entry") else $error("Test failed: Expected 'Third Entry'");

        // Check for a non-existing key
        assert(get_data(4) == "Key not found") else $error("Test failed: Expected 'Key not found'");

        $display("All tests passed.");
        $finish;
    end

endmodule

