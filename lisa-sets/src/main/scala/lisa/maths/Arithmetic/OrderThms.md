[info]   Lemma eqTrans := ( x = y, y = z ) ⊢ x = z
[info]   Theorem leUnfold :=  ⊢ le(m, n) ⇔ ∃(a, a ∈ ℕ ∧ n = m + a)
[info]   Theorem ltUnfold :=  ⊢ lt(m, n) ⇔ ∃(a, a ∈ ℕ ∧ ¬(a = zero) ∧ n = m + a)
[info]   Theorem zeroLe := n ∈ ℕ ⊢ le(zero, n)
[info]   Theorem leZeroIff := n ∈ ℕ ⊢ le(n, zero) ⇔ n = zero
[info]   Theorem ltIrrefl := n ∈ ℕ ⊢ ¬(lt(n, n))
[info]   Theorem ltToNe := ( m ∈ ℕ, n ∈ ℕ, lt(m, n) ) ⊢ ¬(m = n)
[info]   Theorem leAntiSymm := ( m ∈ ℕ, n ∈ ℕ, le(m, n), le(n, m) ) ⊢ m = n
[info]   Theorem ltTrans := ( lt(m, n), lt(n, k), n ∈ ℕ, k ∈ ℕ, m ∈ ℕ ) ⊢ lt(m, k)
[info]   Theorem ltIffLeAndNe := ( m ∈ ℕ, n ∈ ℕ ) ⊢ lt(m, n) ⇔ le(m, n) ∧ ¬(m = n)
[info]   Theorem leRefl := n ∈ ℕ ⊢ le(n, n)
[info]   Theorem leTrans := ( le(m, n), le(n, k), n ∈ ℕ, k ∈ ℕ, m ∈ ℕ ) ⊢ le(m, k)
[info]   Theorem ltImplLe := ( m ∈ ℕ, n ∈ ℕ, lt(m, n) ) ⊢ le(m, n)
[info]   Theorem leToLtOrEq := ( m ∈ ℕ, n ∈ ℕ, le(m, n) ) ⊢ lt(m, n) ∨ m = n
[info]   Theorem addLtMonoRight := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, lt(m, n) ) ⊢ lt(m + k, n + k)
[info]   Theorem addLtMonoLeft := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, lt(m, n) ) ⊢ lt(k + m, k + n)
[info]   Theorem mulLeMonoRight := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, le(m, n) ) ⊢ le(m * k, n * k)
[info]   Theorem mulLeMonoLeft := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, le(m, n) ) ⊢ le(k * m, k * n)
[info]   Theorem mulLtMonoRight := ( lt(m, n), ¬(k = zero), n ∈ ℕ, k ∈ ℕ, m ∈ ℕ ) ⊢ lt(m * k, n * k)
[info]   Theorem mulLtMonoLeft := ( lt(m, n), ¬(k = zero), n ∈ ℕ, k ∈ ℕ, m ∈ ℕ ) ⊢ lt(k * m, k * n)
[info]   Theorem addLeMonoRight := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, le(m, n) ) ⊢ le(m + k, n + k)
[info]   Theorem addLeMonoLeft := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, le(m, n) ) ⊢ le(k + m, k + n)
[info]   Theorem addLeCancelRight := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, le(m + k, n + k) ) ⊢ le(m, n)
[info]   Theorem addLeCancelLeft := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, le(k + m, k + n) ) ⊢ le(m, n)
[info]   Theorem leSucc := n ∈ ℕ ⊢ le(n, Succ(n))
[info]   Theorem zeroLtSucc := n ∈ ℕ ⊢ lt(zero, Succ(n))
[info]   Theorem addLtCancelRight := ( m ∈ ℕ, n ∈ ℕ, k ∈ ℕ, lt(m + k, n + k) ) ⊢ lt(m, n)
[info]   Lemma leUnfold :=  ⊢ le(m, n) ⇔ ∃(w, w ∈ ℕ ∧ n = m + w)
[info]   Lemma ltUnfold :=  ⊢ lt(m, n) ⇔ ∃(w, w ∈ ℕ ∧ ¬(w = zero) ∧ n = m + w)
[info]   Theorem leIntro := ( m ∈ ℕ, n ∈ ℕ, a ∈ ℕ, n = m + a ) ⊢ le(m, n)
[info]   Lemma leElim := le(m, n) ⊢ ∃(w, w ∈ ℕ ∧ n = m + w)
[info]   Theorem ltIntro := ( m ∈ ℕ, ¬(a = zero), a ∈ ℕ, n = m + a, n ∈ ℕ ) ⊢ lt(m, n)
[info]   Lemma ltElim := lt(m, n) ⊢ ∃(w, w ∈ ℕ ∧ ¬(w = zero) ∧ n = m + w)
[info]   Lemma leRefl := n ∈ ℕ ⊢ le(n, n)
[info]   Lemma ltToLe := ( m ∈ ℕ, n ∈ ℕ, lt(m, n) ) ⊢ le(m, n)
[info]   Lemma leTrans := ( le(m, n), le(n, k), n ∈ ℕ, k ∈ ℕ, m ∈ ℕ ) ⊢ le(m, k)
[info]   Theorem zeroLe := n ∈ ℕ ⊢ le(zero, n)
[info]   Theorem leAddRight := ( n ∈ ℕ, k ∈ ℕ ) ⊢ le(n, n + k)
[info]   Theorem leSuccSelf := n ∈ ℕ ⊢ le(n, Succ(n))
[info]   Theorem ltSuccSelf := n ∈ ℕ ⊢ lt(n, Succ(n))
[info]   Theorem ltIrrefl := n ∈ ℕ ⊢ ¬(lt(n, n))
[info]   Lemma ltNeq := ( m ∈ ℕ, n ∈ ℕ, lt(m, n) ) ⊢ ¬(m = n)
[info]   Theorem ltTrans := ( lt(m, n), lt(n, k), n ∈ ℕ, k ∈ ℕ, m ∈ ℕ ) ⊢ lt(m, k)
[info]   Theorem leAntiSym := ( m ∈ ℕ, n ∈ ℕ, le(m, n), le(n, m) ) ⊢ m = n
[info]   Lemma leClosedRight := ( m ∈ ℕ, le(m, n) ) ⊢ n ∈ ℕ
[info]   Lemma ltClosedRight := ( m ∈ ℕ, lt(m, n) ) ⊢ n ∈ ℕ
[info]   Lemma leZeroRightIff := n ∈ ℕ ⊢ le(n, zero) ⇔ n = zero
[info]   Lemma ltZeroFalse := n ∈ ℕ ⊢ ¬(lt(n, zero))
[info]   Lemma leAndNeqToLt := ( m ∈ ℕ, n ∈ ℕ, le(m, n), ¬(m = n) ) ⊢ lt(m, n)
[info]   Lemma ltAsym := ( m ∈ ℕ, n ∈ ℕ, lt(m, n) ) ⊢ ¬(lt(n, m))
[info]   Theorem ltImplLeAndNeq := ( m ∈ ℕ, n ∈ ℕ, lt(m, n) ) ⊢ le(m, n) ∧ ¬(m = n)
[info]   Theorem addZeroLeft := n ∈ ℕ ⊢ zero + n = n
[info]   Theorem addZeroRight := m ∈ ℕ ⊢ m + zero = m
[info]   Theorem addSuccLeft := n ∈ ℕ ⊢ Succ(m) + n = Succ(m + n)
[info]   Theorem addSuccRight := n ∈ ℕ ⊢ m + Succ(n) = Succ(m + n)
[info]   Theorem addComm := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m + n = n + m
[info]   Theorem addOneRight := n ∈ ℕ ⊢ n + Succ(zero) = Succ(n)
[info]   Theorem mulZeroLeft := n ∈ ℕ ⊢ zero * n = zero
[info]   Theorem mulZeroRight := m ∈ ℕ ⊢ m * zero = zero
[info]   Theorem mulSuccRight := n ∈ ℕ ⊢ m * Succ(n) = m * n + m
[info]   Theorem mulOneRight := m ∈ ℕ ⊢ m * Succ(zero) = m
[info]   Theorem mulOneLeft := n ∈ ℕ ⊢ Succ(zero) * n = n
[info]   Theorem addAssoc := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a + b + c = a + b + c
[info]   Theorem mulDistribLeft := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a * b + c = a * b + a * c
[info]   Theorem mulAssoc := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a * b * c = a * b * c
[info]   Theorem mulSuccLeft := ( m ∈ ℕ, n ∈ ℕ ) ⊢ Succ(m) * n = n + m * n
[info]   Theorem mulComm := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m * n = n * m
[info]   Theorem mulDistribRight := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a + b * c = a * c + b * c
[info]   Theorem addLeftCancel := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ, a + b = a + c ) ⊢ b = c
[info]   Theorem addRightCancel := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ, b + a = c + a ) ⊢ b = c
[info]   Theorem addEqSelfZero := ( m ∈ ℕ, n ∈ ℕ, m + n = m ) ⊢ n = zero
[info]   Theorem addEqSelfZeroLeft := ( m ∈ ℕ, n ∈ ℕ, m + n = n ) ⊢ m = zero
[info]   Theorem addClosed3 := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a + b + c ∈ ℕ
[info]   Theorem mulClosed3 := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a * b * c ∈ ℕ
[info]   Theorem mulSuccLeftClosed := ( m ∈ ℕ, n ∈ ℕ ) ⊢ Succ(m) * n ∈ ℕ
[info]   Theorem addEqZeroIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m + n = zero ⇔ m = zero ∧ n = zero
[info]   Theorem mulEqZeroIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m * n = zero ⇔ m = zero ∨ n = zero
[info]   Theorem addEqZeroLeft := ( m ∈ ℕ, n ∈ ℕ, m + n = zero ) ⊢ m = zero
[info]   Theorem addEqZeroRight := ( m ∈ ℕ, n ∈ ℕ, m + n = zero ) ⊢ n = zero
[info]   Theorem addNeZeroLeft := ( m ∈ ℕ, n ∈ ℕ, ¬(m = zero) ) ⊢ ¬(m + n = zero)
[info]   Theorem addNeZeroRight := ( m ∈ ℕ, n ∈ ℕ, ¬(n = zero) ) ⊢ ¬(m + n = zero)
[info]   Theorem mulNeZeroBoth := ( m ∈ ℕ, n ∈ ℕ, ¬(m * n = zero) ) ⊢ ¬(m = zero) ∧ ¬(n = zero)
[info]   Theorem mulNeZero := ( m ∈ ℕ, n ∈ ℕ, ¬(m = zero), ¬(n = zero) ) ⊢ ¬(m * n = zero)
[info]   Theorem addNeZeroIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ ¬(m + n = zero) ⇔ ¬(m = zero) ∨ ¬(n = zero)
[info]   Theorem mulNeZeroIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ ¬(m * n = zero) ⇔ ¬(m = zero) ∧ ¬(n = zero)
[info]   Theorem mulEqSelfIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m * n = m ⇔ m = zero ∨ n = Succ(zero)
[info]   Theorem addEqSelfIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m + n = m ⇔ n = zero
[info]   Theorem addEqSelfIffLeft := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m + n = n ⇔ m = zero
[info]   Theorem addLeftComm := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a + b + c = b + a + c
[info]   Theorem mulLeftComm := ( a ∈ ℕ, b ∈ ℕ, c ∈ ℕ ) ⊢ a * b * c = b * a * c
[info]   Theorem mulEqZeroRightFromLeftNeZero := ( m ∈ ℕ, n ∈ ℕ, m * n = zero, ¬(m = zero) ) ⊢ n = zero
[info]   Theorem mulEqZeroLeftFromRightNeZero := ( m ∈ ℕ, n ∈ ℕ, m * n = zero, ¬(n = zero) ) ⊢ m = zero
[info]   Theorem mulEqSelfRightIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m * n = n ⇔ n = zero ∨ m = Succ(zero)
[info]   Theorem addEqOneIff := ( m ∈ ℕ, n ∈ ℕ ) ⊢ m + n = Succ(zero) ⇔ m = zero ∧ n = Succ(zero) ∨ m = Succ(zero) ∧ n = zero
