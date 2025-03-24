use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::collections::{BTreeMap, HashMap};
use triemap::TrieMap;

fn url_path_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("URL Path Operations");
    
    // Generate URL-like paths
    let url_paths: Vec<String> = vec![
        // API endpoints
        "/api/v1/users",
        "/api/v1/users/create",
        "/api/v1/users/{id}",
        "/api/v1/users/{id}/profile",
        "/api/v1/users/{id}/posts",
        "/api/v1/users/{id}/posts/{post_id}",
        "/api/v1/users/{id}/friends",
        "/api/v1/posts",
        "/api/v1/posts/{id}",
        "/api/v1/posts/{id}/comments",
        "/api/v1/comments/{id}",
        // Website routes
        "/",
        "/home",
        "/about",
        "/contact",
        "/login",
        "/register",
        "/dashboard",
        "/dashboard/settings",
        "/dashboard/profile",
        "/dashboard/messages",
        "/dashboard/messages/{id}",
        "/products",
        "/products/{category}",
        "/products/{category}/{id}",
        "/blog",
        "/blog/{id}",
        "/blog/category/{category}",
        // Admin routes
        "/admin",
        "/admin/users",
        "/admin/posts",
        "/admin/comments",
        "/admin/settings",
        "/admin/analytics",
        // Static files
        "/static/css/main.css",
        "/static/js/app.js",
        "/static/images/logo.png",
        "/static/fonts/roboto.woff",
        "/static/favicon.ico",
    ].into_iter().map(|s| s.to_string()).collect();
    
    let expanded_paths: Vec<String> = url_paths.iter()
        .flat_map(|path| {
            vec![
                path.clone(),
                path.replace("{id}", "12345"),
                path.replace("{id}", "67890").replace("{post_id}", "54321"),
                path.replace("{category}", "electronics"),
            ]
        })
        .collect();
    
    // Common path prefixes to test
    let prefixes = vec![
        "/api",
        "/api/v1/users",
        "/admin",
        "/static",
        "/dashboard",
        "/products",
    ];
    
    // Benchmark path matching
    group.bench_function("insert_all_paths", |b| {
        b.iter(|| {
            let mut trie = TrieMap::new();
            for (i, path) in expanded_paths.iter().enumerate() {
                trie.insert(path, i);
            }
            black_box(trie)
        })
    });
    
    // Build trie once for further tests
    let mut trie = TrieMap::new();
    for (i, path) in expanded_paths.iter().enumerate() {
        trie.insert(path, i);
    }
    
    // Exact matches
    group.bench_function("exact_path_matches", |b| {
        let lookup_paths = expanded_paths.clone();
        b.iter(|| {
            let mut found = 0;
            for path in &lookup_paths {
                if trie.get(path).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    // Prefix searches
    group.bench_function("prefix_searches", |b| {
        b.iter(|| {
            let mut total_matches = 0;
            for prefix in &prefixes {
                total_matches += trie.get_prefix_matches(prefix).len();
            }
            black_box(total_matches)
        })
    });
    
    // Compare with HashMap and BTreeMap for route matching
    let mut hash_map = HashMap::new();
    let mut btree_map = BTreeMap::new();
    for (i, path) in expanded_paths.iter().enumerate() {
        hash_map.insert(path.clone(), i);
        btree_map.insert(path.clone(), i);
    }
    
    group.bench_function("hash_map_exact_matches", |b| {
        let lookup_paths = expanded_paths.clone();
        b.iter(|| {
            let mut found = 0;
            for path in &lookup_paths {
                if hash_map.get(path).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    group.bench_function("btree_map_exact_matches", |b| {
        let lookup_paths = expanded_paths.clone();
        b.iter(|| {
            let mut found = 0;
            for path in &lookup_paths {
                if btree_map.get(path).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    // Hash and BTree maps don't have built-in prefix search, so we simulate it
    group.bench_function("hash_map_prefix_searches", |b| {
        b.iter(|| {
            let mut total_matches = 0;
            for prefix in &prefixes {
                for (path, _) in &hash_map {
                    if path.starts_with(prefix) {
                        total_matches += 1;
                    }
                }
            }
            black_box(total_matches)
        })
    });
    
    group.bench_function("btree_map_prefix_searches", |b| {
        b.iter(|| {
            let mut total_matches = 0;
            for prefix in &prefixes {
                for (path, _) in btree_map.range(prefix.to_string()..) {
                    if path.starts_with(prefix) {
                        total_matches += 1;
                    } else {
                        break;
                    }
                }
            }
            black_box(total_matches)
        })
    });
    
    group.finish();
}

fn dictionary_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Dictionary Operations");
    
    // Generate dictionary-like data (common English words)
    // This is a small sample; in a real benchmark, you'd have thousands of words
    let common_words = vec![
        "the", "be", "to", "of", "and", "a", "in", "that", "have", "I",
        "it", "for", "not", "on", "with", "he", "as", "you", "do", "at",
        "this", "but", "his", "by", "from", "they", "we", "say", "her", "she",
        "or", "an", "will", "my", "one", "all", "would", "there", "their", "what",
        "so", "up", "out", "if", "about", "who", "get", "which", "go", "me",
        "when", "make", "can", "like", "time", "no", "just", "him", "know", "take",
        "people", "into", "year", "your", "good", "some", "could", "them", "see", "other",
        "than", "then", "now", "look", "only", "come", "its", "over", "think", "also",
        "back", "after", "use", "two", "how", "our", "work", "first", "well", "way",
        "even", "new", "want", "because", "any", "these", "give", "day", "most", "us",
    ];
    
    // Duplicate and modify to make a larger dataset
    let expanded_words: Vec<String> = common_words.iter()
        .flat_map(|word| {
            vec![
                word.to_string(),
                format!("{}s", word),
                format!("{}ing", word),
                format!("{}ed", word),
                format!("un{}", word),
                format!("re{}", word),
                format!("{}ness", word),
                format!("{}ful", word),
            ]
        })
        .collect();
    
    // Prefixes to search for
    let prefixes = vec!["a", "b", "c", "d", "un", "re", "th", "ing", "ed", "s"];
    
    // Build maps for benchmarking
    let mut trie = TrieMap::new();
    let mut hash_map = HashMap::new();
    let mut btree_map = BTreeMap::new();
    
    for (i, word) in expanded_words.iter().enumerate() {
        trie.insert(word, i);
        hash_map.insert(word.clone(), i);
        btree_map.insert(word.clone(), i);
    }
    
    // Benchmark dictionary lookups
    let lookup_words: Vec<String> = expanded_words.iter()
        .enumerate()
        .filter(|(i, _)| i % 3 == 0)
        .map(|(_, word)| word.clone())
        .chain(vec!["nonexistent1", "nonexistent2", "nonexistent3"].into_iter().map(|s| s.to_string()))
        .collect();
    
    group.bench_function("trie_lookups", |b| {
        b.iter(|| {
            let mut found = 0;
            for word in &lookup_words {
                if trie.get(word).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    group.bench_function("hash_map_lookups", |b| {
        b.iter(|| {
            let mut found = 0;
            for word in &lookup_words {
                if hash_map.get(word).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    group.bench_function("btree_map_lookups", |b| {
        b.iter(|| {
            let mut found = 0;
            for word in &lookup_words {
                if btree_map.get(word).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    // Benchmark prefix matching (autocomplete)
    group.bench_function("trie_prefix_matches", |b| {
        b.iter(|| {
            let mut total_matches = 0;
            for prefix in &prefixes {
                total_matches += trie.get_prefix_matches(prefix).len();
            }
            black_box(total_matches)
        })
    });
    
    group.bench_function("hash_map_prefix_matches", |b| {
        b.iter(|| {
            let mut total_matches = 0;
            for prefix in &prefixes {
                for (word, _) in &hash_map {
                    if word.starts_with(prefix) {
                        total_matches += 1;
                    }
                }
            }
            black_box(total_matches)
        })
    });
    
    group.bench_function("btree_map_prefix_matches", |b| {
        b.iter(|| {
            let mut total_matches = 0;
            for prefix in &prefixes {
                for (word, _) in btree_map.range(prefix.to_string()..) {
                    if word.starts_with(prefix) {
                        total_matches += 1;
                    } else {
                        break;
                    }
                }
            }
            black_box(total_matches)
        })
    });
    
    group.finish();
}

fn file_path_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("File Path Operations");
    
    // Generate typical file path structure
    let base_paths = vec![
        "src/main.rs",
        "src/lib.rs",
        "src/utils/mod.rs",
        "src/utils/helpers.rs",
        "src/models/mod.rs",
        "src/models/user.rs",
        "src/models/post.rs",
        "src/controllers/mod.rs",
        "src/controllers/user_controller.rs",
        "src/controllers/post_controller.rs",
        "tests/main_test.rs",
        "tests/utils_test.rs",
        "tests/models/user_test.rs",
        "tests/models/post_test.rs",
        "docs/README.md",
        "docs/CONTRIBUTING.md",
        "docs/API.md",
        "build/debug/main",
        "build/release/main",
        "config/dev.json",
        "config/prod.json",
    ];
    
    // Expand to create a larger dataset
    let expanded_paths: Vec<String> = base_paths.iter()
        .flat_map(|path| {
            let mut paths = vec![path.to_string()];
            
            // Add some variations
            if path.contains("src/") {
                paths.push(path.replace("src/", "src/v2/"));
                paths.push(path.replace("src/", "src/legacy/"));
            }
            
            if path.contains("tests/") {
                paths.push(path.replace("tests/", "tests/integration/"));
                paths.push(path.replace("tests/", "tests/unit/"));
            }
            
            paths
        })
        .collect();
    
    // Common directory prefixes
    let prefixes = vec!["src/", "src/models", "tests/", "docs/", "config/", "build/"];
    
    // Build data structures
    let mut trie = TrieMap::new();
    let mut hash_map = HashMap::new();
    let mut btree_map = BTreeMap::new();
    
    for (i, path) in expanded_paths.iter().enumerate() {
        trie.insert(path, i);
        hash_map.insert(path.clone(), i);
        btree_map.insert(path.clone(), i);
    }
    
    // Benchmark directory listing (prefix search)
    group.bench_function("trie_directory_listing", |b| {
        b.iter(|| {
            let mut total_paths = 0;
            for prefix in &prefixes {
                total_paths += trie.get_prefix_matches(prefix).len();
            }
            black_box(total_paths)
        })
    });
    
    group.bench_function("hash_map_directory_listing", |b| {
        b.iter(|| {
            let mut total_paths = 0;
            for prefix in &prefixes {
                for (path, _) in &hash_map {
                    if path.starts_with(prefix) {
                        total_paths += 1;
                    }
                }
            }
            black_box(total_paths)
        })
    });
    
    group.bench_function("btree_map_directory_listing", |b| {
        b.iter(|| {
            let mut total_paths = 0;
            for prefix in &prefixes {
                for (path, _) in btree_map.range(prefix.to_string()..) {
                    if path.starts_with(prefix) {
                        total_paths += 1;
                    } else {
                        break;
                    }
                }
            }
            black_box(total_paths)
        })
    });
    
    // Benchmark file lookup
    let lookup_paths: Vec<String> = expanded_paths.iter()
        .enumerate()
        .filter(|(i, _)| i % 3 == 0)
        .map(|(_, path)| path.clone())
        .chain(vec!["nonexistent/file.txt", "another/missing/file.rs"].into_iter().map(|s| s.to_string()))
        .collect();
    
    group.bench_function("trie_file_lookup", |b| {
        b.iter(|| {
            let mut found = 0;
            for path in &lookup_paths {
                if trie.get(path).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    group.bench_function("hash_map_file_lookup", |b| {
        b.iter(|| {
            let mut found = 0;
            for path in &lookup_paths {
                if hash_map.get(path).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    group.bench_function("btree_map_file_lookup", |b| {
        b.iter(|| {
            let mut found = 0;
            for path in &lookup_paths {
                if btree_map.get(path).is_some() {
                    found += 1;
                }
            }
            black_box(found)
        })
    });
    
    group.finish();
}

criterion_group!(
    real_world_benches,
    url_path_benchmarks,
    dictionary_benchmarks,
    file_path_benchmarks
);
criterion_main!(real_world_benches);
