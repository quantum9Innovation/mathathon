#!/usr/bin/env perl
# Verify the configuration-model first moment in combinatorics-21.txt.
use strict;
use warnings;
use POSIX qw(lgamma);

sub log_choose {
    my ($n, $k) = @_;
    return lgamma($n+1)-lgamma($k+1)-lgamma($n-$k+1);
}

sub log_odd_double_factorial {
    my ($twice_count) = @_;
    die "Invalid double factorial" if $twice_count<0 || $twice_count%2;
    my $half=$twice_count/2;
    return lgamma($twice_count+1)-$half*log(2)-lgamma($half+1);
}

sub log_term {
    my ($n, $k, $r) = @_;
    my $q=2*$r*log(2)+lgamma($r+1)
        +log_odd_double_factorial(2*$k-$r)
        +log_odd_double_factorial(2*($n-$k)-$r)
        -log_odd_double_factorial(2*$n);
    return log_choose($n,$k)+log_choose($k,$r)
        +log_choose($n-$k,$r)+2*$q;
}

for my $n (20,50,100,200,500,1000) {
    my @terms;
    for my $k (2..int($n/2)) {
        for (my $r=0; $r<=$k; $r+=2) {
            push @terms, log_term($n,$k,$r);
        }
    }
    my $largest=$terms[0];
    for (@terms) {$largest=$_ if $_>$largest;}
    my $sum=0;
    for (@terms) {$sum+=exp($_-$largest);}
    my $first_moment=exp($largest)*$sum;
    printf "N=%4d E_config[k=2..N/2]=%.9g N^2*E=%.9g\n",
        $n,$first_moment,$n*$n*$first_moment;
}
