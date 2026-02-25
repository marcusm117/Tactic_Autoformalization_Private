#!/usr/bin/env python3
"""
Analyze the domain distribution in Omni-MATH dataset.
"""

import json
from collections import defaultdict
from pathlib import Path


def analyze_domains(jsonl_path: str):
    """Analyze domain distribution from Omni-MATH JSONL file."""

    # Read all domains from the JSONL file
    domains = []
    with open(jsonl_path, 'r') as f:
        for line in f:
            data = json.loads(line)
            domains.extend(data.get('domain', []))

    # Count by main domain and subdomain
    main_domain_counts = defaultdict(int)
    subdomain_counts = defaultdict(int)
    full_path_counts = defaultdict(int)

    for domain in domains:
        parts = [p.strip() for p in domain.split('->')]

        # Main domain (e.g., "Mathematics")
        if len(parts) >= 1:
            main_domain_counts[parts[0]] += 1

        # Subdomain (e.g., "Algebra")
        if len(parts) >= 2:
            subdomain_counts[parts[1]] += 1

        # Full path
        full_path_counts[domain] += 1

    # Organize by subdomain for detailed breakdown
    subdomain_breakdown = defaultdict(lambda: defaultdict(int))
    for path, count in full_path_counts.items():
        parts = [p.strip() for p in path.split('->')]
        if len(parts) >= 2:
            subdomain = parts[1]
            rest = ' -> '.join(parts[2:]) if len(parts) > 2 else "(no sub-category)"
            subdomain_breakdown[subdomain][rest] = count

    return {
        'total_problems': len(domains),
        'unique_paths': len(full_path_counts),
        'main_domain_counts': dict(main_domain_counts),
        'subdomain_counts': dict(subdomain_counts),
        'full_path_counts': dict(full_path_counts),
        'subdomain_breakdown': {k: dict(v) for k, v in subdomain_breakdown.items()}
    }


def print_report(results: dict):
    """Print a formatted report of the analysis."""

    print("=" * 100)
    print("DOMAIN DISTRIBUTION ANALYSIS")
    print("=" * 100)
    print(f"\nTotal problems: {results['total_problems']}")
    print(f"Total unique paths: {results['unique_paths']}")

    print("\n" + "=" * 100)
    print("MAIN DOMAINS")
    print("=" * 100)
    for domain, count in sorted(results['main_domain_counts'].items(), key=lambda x: -x[1]):
        print(f"  {domain}: {count}")

    print("\n" + "=" * 100)
    print("SUBDOMAINS")
    print("=" * 100)
    for subdomain, count in sorted(results['subdomain_counts'].items(), key=lambda x: -x[1]):
        print(f"  {subdomain}: {count}")

    print("\n" + "=" * 100)
    print("DETAILED BREAKDOWN BY SUBDOMAIN")
    print("=" * 100)

    # Order subdomains by count
    ordered_subdomains = sorted(
        results['subdomain_counts'].keys(),
        key=lambda x: -results['subdomain_counts'][x]
    )

    for subdomain in ordered_subdomains:
        if subdomain in results['subdomain_breakdown']:
            total = results['subdomain_counts'][subdomain]
            print(f"\n{'='*100}")
            print(f"{subdomain} (Total: {total})")
            print("=" * 100)
            for subpath, count in sorted(
                results['subdomain_breakdown'][subdomain].items(),
                key=lambda x: -x[1]
            ):
                print(f"  {count:4d}  {subpath}")


def main():
    # Default path - modify as needed
    script_dir = Path(__file__).parent
    project_root = script_dir.parent.parent  # Go up to 00_Tactic_Autoformalization_Private
    jsonl_path = project_root / "data" / "Omni-MATH.jsonl"

    if not jsonl_path.exists():
        print(f"Error: File not found: {jsonl_path}")
        return

    results = analyze_domains(str(jsonl_path))
    print_report(results)

    # Optionally save results to JSON
    output_path = project_root / "data" / "omnimath_domain_analysis.json"
    with open(output_path, 'w') as f:
        json.dump(results, f, indent=2)
    print(f"\n\nResults saved to: {output_path}")


if __name__ == "__main__":
    main()
