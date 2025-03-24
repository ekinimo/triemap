use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion};
use std::collections::{BTreeMap, HashMap};
use triemap::TrieMap;

fn insert_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Insert Operations");
    
    // Benchmark with small keys (1-5 chars)
    let small_keys: Vec<String> = (0..1000)
        .map(|i| format!("k{:03}", i % 100))
        .collect();
        
    // Benchmark with medium keys (10-15 chars)
    let medium_keys: Vec<String> = (0..1000)
        .map(|i| format!("medium_key_{:05}", i % 100))
        .collect();
        
    // Benchmark with long keys (30+ chars)
    let long_keys: Vec<String> = (0..1000)
        .map(|i| format!("this_is_a_very_long_key_for_benchmarking_{:05}", i % 100))
        .collect();

    for size in [100, 500, 1000].iter() {
        // Small keys
        group.bench_with_input(
            BenchmarkId::new("HashMap/small_keys", size), 
            &small_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = HashMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("BTreeMap/small_keys", size), 
            &small_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = BTreeMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/small_keys", size), 
            &small_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = TrieMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        // Medium keys
        group.bench_with_input(
            BenchmarkId::new("HashMap/medium_keys", size), 
            &medium_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = HashMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("BTreeMap/medium_keys", size), 
            &medium_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = BTreeMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/medium_keys", size), 
            &medium_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = TrieMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        // Long keys
        group.bench_with_input(
            BenchmarkId::new("HashMap/long_keys", size), 
            &long_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = HashMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("BTreeMap/long_keys", size), 
            &long_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = BTreeMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/long_keys", size), 
            &long_keys[..*size], 
            |b, keys| {
                b.iter(|| {
                    let mut map = TrieMap::new();
                    for (i, key) in keys.iter().enumerate() {
                        map.insert(key, i);
                    }
                    black_box(map)
                })
            }
        );
    }
    
    group.finish();
}

fn lookup_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Lookup Operations");
    
    // Create dataset with keys of varying length
    let keys: Vec<String> = (0..1000)
        .map(|i| {
            if i % 3 == 0 {
                format!("k{:03}", i % 100)
            } else if i % 3 == 1 {
                format!("medium_key_{:05}", i % 100)
            } else {
                format!("this_is_a_very_long_key_for_benchmarking_{:05}", i % 100)
            }
        })
        .collect();

    // Prepare lookup keys (mix of hits and misses)
    let lookup_keys: Vec<String> = keys.iter()
        .enumerate()
        .filter(|(i, _)| i % 5 < 4) // 80% hit rate
        .map(|(_, k)| k.clone())
        .chain((0..200).map(|i| format!("nonexistent_key_{}", i))) // 20% miss rate
        .collect();

    let lookup_count = lookup_keys.len();
    
    for &size in &[100, 500, 1000] {
        // Prepare maps
        let mut hash_map = HashMap::new();
        let mut btree_map = BTreeMap::new();
        let mut trie_map = TrieMap::new();
        
        for (i, key) in keys.iter().take(size).enumerate() {
            hash_map.insert(key.clone(), i);
            btree_map.insert(key.clone(), i);
            trie_map.insert(key, i);
        }
        
        // Benchmark lookups
        group.bench_with_input(
            BenchmarkId::new("HashMap/lookup", size),
            &lookup_keys,
            |b, lookup_keys| {
                b.iter(|| {
                    let mut found = 0;
                    for key in lookup_keys {
                        if hash_map.get(key).is_some() {
                            found += 1;
                        }
                    }
                    black_box(found)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("BTreeMap/lookup", size),
            &lookup_keys,
            |b, lookup_keys| {
                b.iter(|| {
                    let mut found = 0;
                    for key in lookup_keys {
                        if btree_map.get(key).is_some() {
                            found += 1;
                        }
                    }
                    black_box(found)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/lookup", size),
            &lookup_keys,
            |b, lookup_keys| {
                b.iter(|| {
                    let mut found = 0;
                    for key in lookup_keys {
                        if trie_map.get(key).is_some() {
                            found += 1;
                        }
                    }
                    black_box(found)
                })
            }
        );
    }
    
    group.finish();
}

fn prefix_operation_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Prefix Operations");
    
    // Create dataset with common prefixes
    let prefixed_keys: Vec<String> = (0..1000)
        .map(|i| {
            let prefix = match i % 5 {
                0 => "app",
                1 => "ban",
                2 => "cat",
                3 => "dog",
                _ => "ele",
            };
            
            format!("{}_{:05}", prefix, i)
        })
        .collect();
    
    let prefixes = vec!["app", "ban", "cat", "dog", "ele"];
    
    for &size in &[100, 500, 1000] {
        // Prepare maps
        let mut trie_map = TrieMap::new();
        
        for (i, key) in prefixed_keys.iter().take(size).enumerate() {
            trie_map.insert(key, i);
        }
        
        // Benchmark prefix operations
        group.bench_with_input(
            BenchmarkId::new("TrieMap/prefix_lookup", size),
            &prefixes,
            |b, prefixes| {
                b.iter(|| {
                    let mut total_matches = 0;
                    for &prefix in prefixes.iter() {
                        total_matches += trie_map.get_prefix_matches(prefix).len();
                    }
                    black_box(total_matches)
                })
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/starts_with", size),
            &prefixes,
            |b, prefixes| {
                b.iter(|| {
                    let mut count = 0;
                    for &prefix in prefixes.iter() {
                        if trie_map.starts_with(prefix) {
                            count += 1;
                        }
                    }
                    black_box(count)
                })
            }
        );
    }
    
    group.finish();
}

fn removal_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Remove Operations");
    
    // Create dataset with varying key lengths
    let keys: Vec<String> = (0..1000)
        .map(|i| {
            if i % 3 == 0 {
                format!("k{:03}", i % 100)
            } else if i % 3 == 1 {
                format!("medium_key_{:05}", i % 100)
            } else {
                format!("this_is_a_very_long_key_for_benchmarking_{:05}", i % 100)
            }
        })
        .collect();
    
    for &size in &[100, 500, 1000] {
        // Prepare removal keys (half of the dataset)
        let removal_keys: Vec<String> = keys.iter()
            .take(size)
            .enumerate()
            .filter(|(i, _)| i % 2 == 0)
            .map(|(_, k)| k.clone())
            .collect();
        
        // Benchmark removals
        group.bench_with_input(
            BenchmarkId::new("HashMap/remove", size),
            &removal_keys,
            |b, removal_keys| {
                b.iter_with_setup(
                    || {
                        let mut map = HashMap::new();
                        for (i, key) in keys.iter().take(size).enumerate() {
                            map.insert(key.clone(), i);
                        }
                        map
                    },
                    |mut map| {
                        for key in removal_keys {
                            map.remove(key);
                        }
                        black_box(map)
                    }
                )
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("BTreeMap/remove", size),
            &removal_keys,
            |b, removal_keys| {
                b.iter_with_setup(
                    || {
                        let mut map = BTreeMap::new();
                        for (i, key) in keys.iter().take(size).enumerate() {
                            map.insert(key.clone(), i);
                        }
                        map
                    },
                    |mut map| {
                        for key in removal_keys {
                            map.remove(key);
                        }
                        black_box(map)
                    }
                )
            }
        );
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/remove", size),
            &removal_keys,
            |b, removal_keys| {
                b.iter_with_setup(
                    || {
                        let mut map = TrieMap::new();
                        for (i, key) in keys.iter().take(size).enumerate() {
                            map.insert(key, i);
                        }
                        map
                    },
                    |mut map| {
                        for key in removal_keys {
                            map.remove(key);
                        }
                        black_box(map)
                    }
                )
            }
        );
        
        // Prefix-based removal (TrieMap only)
        let prefix_removals = vec!["k", "medium", "this_is"];
        
        group.bench_with_input(
            BenchmarkId::new("TrieMap/remove_prefix", size),
            &prefix_removals,
            |b, prefixes| {
                b.iter_with_setup(
                    || {
                        let mut map = TrieMap::new();
                        for (i, key) in keys.iter().take(size).enumerate() {
                            map.insert(key, i);
                        }
                        map
                    },
                    |mut map| {
                        for &prefix in prefixes {
                            map.remove_prefix_matches(prefix);
                        }
                        black_box(map)
                    }
                )
            }
        );
    }
    
    group.finish();
}

fn iteration_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Iteration");
    
    // Create dataset
    let keys: Vec<String> = (0..1000)
        .map(|i| format!("key_{:05}", i))
        .collect();
    
    for &size in &[100, 500, 1000] {
        // HashMap iteration
        group.bench_with_input(
            BenchmarkId::new("HashMap/iter", size),
            &size,
            |b, &size| {
                let mut map = HashMap::new();
                for (i, key) in keys.iter().take(size).enumerate() {
                    map.insert(key.clone(), i);
                }
                
                b.iter(|| {
                    let mut sum = 0;
                    for (_, &value) in map.iter() {
                        sum += value;
                    }
                    black_box(sum)
                })
            }
        );
        
        // BTreeMap iteration
        group.bench_with_input(
            BenchmarkId::new("BTreeMap/iter", size),
            &size,
            |b, &size| {
                let mut map = BTreeMap::new();
                for (i, key) in keys.iter().take(size).enumerate() {
                    map.insert(key.clone(), i);
                }
                
                b.iter(|| {
                    let mut sum = 0;
                    for (_, &value) in map.iter() {
                        sum += value;
                    }
                    black_box(sum)
                })
            }
        );
        
        // TrieMap iteration
        group.bench_with_input(
            BenchmarkId::new("TrieMap/iter", size),
            &size,
            |b, &size| {
                let mut map = TrieMap::new();
                for (i, key) in keys.iter().take(size).enumerate() {
                    map.insert(key, i);
                }
                
                b.iter(|| {
                    let mut sum = 0;
                    for (_, &value) in map.iter() {
                        sum += value;
                    }
                    black_box(sum)
                })
            }
        );
    }
    
    group.finish();
}

criterion_group!(
    benches, 
    insert_benchmarks,
    lookup_benchmarks,
    prefix_operation_benchmarks,
    removal_benchmarks,
    iteration_benchmarks
);
criterion_main!(benches);
