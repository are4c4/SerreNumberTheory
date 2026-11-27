import SerreNumberTheory.Chapter01.S010101FiniteFields

namespace SerreNumberTheory

open Finset
open Subgroup

/-!
# 有限体の乗法群（S1.1.2）

Serre の証明と Notion のメモに合わせ，次の順で形式化する．
1. 巡回群の部分群の存在と一意性
2. 巡回群の生成元の個数と Euler 関数
3. 補題1：Euler 関数の総和公式
4. 補題2：有限群が巡回群となるための判定
5. 定理2：有限体の乗法群の巡回性

`Nat.sum_totient`，`isCyclic_of_card_pow_eq_one_le`，
`IsCyclic.card_orderOf_eq_totient` は証明に使わない．
基本的な群論・有限集合の定理は Mathlib から引用する．
-/

/-!
## 生成部分群と元の位数
-/

section GeneratedSubgroup

-- H を有限群とする
variable (H : Type*) [Group H] [Fintype H]

/--
元 x が生成する部分群の位数は x の位数に等しい．
（mathlibの定理をほぼそのまま使用）
（後で使いやすいようにFintype.cardからNat.cardに変換）
-/
theorem zpowers_card (x : H) :
    Nat.card (Subgroup.zpowers x) = orderOf x := by
      -- Subgroup.zpowers x : 元xによって生成される部分群 { xᵏ | k ∈ ℤ }
        -- zpowersのzは整数，powersは累乗を意味する
      -- orderOf x : 元xの位数
  rw [Nat.card_eq_fintype_card]
    --  Nat.card_eq_fintype_card : Nat.card α = Fintype.card α
  exact Fintype.card_zpowers
    -- Fintype.card_zpowers : 元 x が生成する部分群の位数は x の位数に等しい

/--
位数 n の群で，位数 n の元があればその元は生成元である．
-/
theorem zpowers_eq_top_of_orderOf_eq_card
    (x : H) (hx : orderOf x = Fintype.card H) :
    Subgroup.zpowers x = (⊤ : Subgroup H) := by
      -- (⊤ : Subgroup H) : Hの部分群全体の順序集合の最大元
        -- ここでは包含関係を順序としているので，最大元はH自身となる
        -- (Subgroup.zpowers x : Subgroup H)と型を合わせるために，Hではなく⊤を使う
  apply Subgroup.eq_top_of_le_card
    -- Subgroup.eq_top_of_le_card : 有限群Hの部分群Cに対して，|H| ≤ |C| => C = H
  rw [zpowers_card H x, hx, Nat.card_eq_fintype_card]

/--
x^d = 1 ならば <x> の任意の元も d 乗して 1 になる．
-/
theorem pow_eq_one_of_mem_zpowers
    (x y : H) (d : ℕ) (hx : x ^ d = 1) (hy : y ∈ Subgroup.zpowers x) :
    y ^ d = 1 := by
  obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr hy
    -- mem_powers_iff_mem_zpowers : y ∈ Submonoid.powers x ↔ y ∈ zpowers x
      -- Submonoid.powers x : xの非負整数乗全体
      -- Subgroup.zpowers x : xの整数乗全体
    -- obtain : 存在命題から k : ℕ , hk : xᵏ = y を取り出す
  change x ^ k = y at hk
    -- hk : (fun i => x ^ i) k = y → hk : x ^ k = y に書き換える
  calc
    y ^ d
      = (x ^ k) ^ d := by
          rw [← hk]
    _ = x ^ (k * d) := by
          rw [pow_mul]
    _ = x ^ (d * k) := by
          rw [Nat.mul_comm k d]
    _ = (x ^ d) ^ k := by
          rw [pow_mul]
    _ = (1 : H) ^ k := by
          rw [hx]
    _ = 1 := by
          exact one_pow k

end GeneratedSubgroup

/-! ## 巡回群の部分群の存在と一意性 -/

section CyclicSubgroups

-- G を有限巡回群とする
variable (G : Type*) [Group G] [Fintype G] [IsCyclic G]
  -- [IsCyclic G] : Gを巡回群とする

omit [IsCyclic G] in
/--
位数 n の巡回群の生成元 g について，g^(n/d) の位数は d である．
-/
theorem orderOf_pow_div
    (g : G) (hg : orderOf g = Fintype.card G) (d : ℕ) (hd : d ∣ Fintype.card G) :
    orderOf (g ^ (Fintype.card G / d)) = d := by
  let n := Fintype.card G
  let q := n / d
  have hn : 0 < n := by
    exact Fintype.card_pos
      -- Fintype.card_pos : 0 < Fintype.card α
  have hgn : orderOf g = n := by
    exact hg
  have hqd : q * d = n := by
    exact Nat.div_mul_cancel hd
  have hq_dvd : q ∣ n := by
    exact Nat.div_dvd_of_dvd hd
      -- Nat.div_dvd_of_dvd : n ∣ m => m / n ∣ m
        -- ここでは，d ∣ n → (n / d) ∣ n
  have hqpos : 0 < q := by
    exact Nat.pos_of_dvd_of_pos hq_dvd hn
      -- Nat.pos_of_dvd_of_pos : m n : ℕ, m ∣ n, 0 < n => 0 < m

  -- 【ord(g^q) | d】(g^q)^d = g^n = 1
  have hpow : (g ^ q) ^ d = 1 := by
    rw [← pow_mul, hqd, ← hgn]
    exact pow_orderOf_eq_one g
      -- pow_orderOf_eq_one x : x ^ orderOf x = 1
  have h₁ : orderOf (g ^ q) ∣ d := by
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
      -- orderOf_dvd_iff_pow_eq_one : orderOf x ∣ n ↔ x ^ n = 1

  -- 【d | ord(g^q)】m := ord(g^q) とおくと g^(qm) = 1
  let m := orderOf (g ^ q)
  have hgm : g ^ (q * m) = 1 := by
    rw [pow_mul]
    exact pow_orderOf_eq_one (g ^ q)
  have hnDiv : n ∣ q * m := by
    rw [← hgn]
    exact orderOf_dvd_iff_pow_eq_one.mpr hgm
  -- n = q*d なので，q>0 を用いて q を約分する
  have h₂ : d ∣ m := by
    apply Nat.dvd_of_mul_dvd_mul_right hqpos
      -- Nat.dvd_of_mul_dvd_mul_right : 0 < k, m * k ∣ n * k => m ∣ n
    rw [Nat.mul_comm d q, hqd, Nat.mul_comm m q]
    exact hnDiv

  -- 【ord(g^q) | d】かつ【d | ord(g^q)】だから ord(g^q) = d．
  exact Nat.dvd_antisymm h₁ h₂
    -- Nat.dvd_antisymm : m ∣ n, n ∣ m => m = n

omit [IsCyclic G] in
/--
G = <g> のとき，d 乗して 1 になる元は <g^(n/d)> に属する．
-/
theorem mem_cyclicSubgroup_of_pow_eq_one
    (g : G) (hg : ∀ y : G, y ∈ Subgroup.zpowers g)
    (d : ℕ) (hd : d ∣ Fintype.card G)
    (y : G) (hy : y ^ d = 1) :
    y ∈ Subgroup.zpowers (g ^ (Fintype.card G / d)) := by
  let n := Fintype.card G
  have hn : 0 < n := by
    exact Fintype.card_pos
  have hdpos : 0 < d := by
    exact Nat.pos_of_dvd_of_pos hd hn
  have hgord : orderOf g = n := by
    calc
      orderOf g
        = Nat.card G := by
          exact orderOf_eq_card_of_forall_mem_zpowers hg
            -- orderOf_eq_card_of_forall_mem_zpowers : 有限群の生成元の位数は、群の位数に等しい
      _ = n := by
          exact Nat.card_eq_fintype_card

  -- G は巡回群なので，ある k が存在して y = g^k と書ける．
  obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr (hg y))

  -- hk の形を (fun i => g ^ i) k = y から g ^ k = y に直す．
  change g ^ k = y at hk

  -- g^(kd) = 1 から n | kd を得る．
  have hpow : g ^ (k * d) = 1 := by
    rw [pow_mul, hk]
    exact hy
  have hdiv : n ∣ k * d := by
    rw [← hgord]
    exact orderOf_dvd_iff_pow_eq_one.mpr hpow
      -- orderOf_dvd_iff_pow_eq_one : (orderOf x) ∣ n ↔ x ^ n = 1

  -- n = (n/d)d なので d を約分すると (n/d) | k．
  have hnd : n / d * d = n := by
    exact Nat.div_mul_cancel hd
  have hqdiv : n / d ∣ k := by
    apply Nat.dvd_of_mul_dvd_mul_right hdpos
    rw [hnd]
    exact hdiv

  -- n / d ∣ k だから，ある l が存在して，k = (n/d)^l と表せる．
  obtain ⟨l, hl⟩ := hqdiv

  have hyEq : y = (g ^ (n / d)) ^ l := by
    calc
      y = g ^ k := by
        exact hk.symm
      _ = g ^ ((n / d) * l) := by
          rw [hl]
      _ = (g ^ (n / d)) ^ l := by
          exact pow_mul g (n / d) l
  rw [hyEq]
  exact Subgroup.npow_mem_zpowers _ _
    -- Subgroup.npow_mem_zpowers : 群の元 x の任意の自然数乗は、x が生成する部分群に属する

/--
位数 n の巡回群には，各 d | n に対して位数 d の部分群がただ一つ存在する．
-/
theorem cyclic_subgroup_existsUnique
    (d : ℕ) (hd : d ∣ Fintype.card G) :
    ∃! C : Subgroup G, Nat.card C = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  let C_d : Subgroup G := Subgroup.zpowers (g ^ (Fintype.card G / d))

  -- 【存在】C_d の位数は d．
  have hCd : Nat.card C_d = d := by
    change Nat.card (Subgroup.zpowers (g ^ (Fintype.card G / d))) = d
    rw [zpowers_card]
    exact orderOf_pow_div G g hgord d hd
  refine ⟨C_d, hCd, ?_⟩

  -- 【一意性】任意の位数 d の部分群 C を取る．
  intro C hC
  have hle : C ≤ C_d := by
    intro y hy
    -- ラグランジュの定理を部分群 C に適用する．
    let z : C := ⟨y, hy⟩
    have hz : z ^ d = 1 := by
      rw [← hC]
      exact pow_card_eq_one'
    have hyPow : y ^ d = 1 := by
      exact congrArg (fun t : C => (t : G)) hz
    -- y^d = 1 なので y ∈ C_d．
    exact mem_cyclicSubgroup_of_pow_eq_one G g hg d hd y hyPow

  -- C ⊆ C_d かつ |C| = |C_d| = d．
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hC, hCd]

end CyclicSubgroups

/-! ## 生成元集合と Euler 関数 -/

section Generators

variable (H : Type*) [Group H] [Fintype H] [DecidableEq H]

/-- 部分群 C の生成元全体（ambient group H の元として集める）． -/
noncomputable def generators (C : Subgroup H) : Finset H := by
  classical
  exact Finset.univ.filter (fun y : H => Subgroup.zpowers y = C)

/-- y ∈ Φ_C と <y> = C は同値．後者から y ∈ C も従う． -/
theorem mem_generators_iff (C : Subgroup H) (y : H) :
    y ∈ generators H C ↔ Subgroup.zpowers y = C := by
  classical
  simp [generators]

/-- x^k が <x> を生成することと gcd(ord(x), k) = 1 は同値． -/
theorem pow_generates_iff_coprime (x : H) (k : ℕ) :
    Subgroup.zpowers (x ^ k) = Subgroup.zpowers x ↔
      (orderOf x).Coprime k := by
  -- <x^k> ⊆ <x> は常に成立する．
  have hle : Subgroup.zpowers (x ^ k) ≤ Subgroup.zpowers x := by
    apply Subgroup.zpowers_le_of_mem
    exact Subgroup.npow_mem_zpowers x k
  -- 逆の包含は x ∈ <x^k> と同値．
  have heq : Subgroup.zpowers (x ^ k) = Subgroup.zpowers x ↔
      x ∈ Subgroup.zpowers (x ^ k) := by
    constructor
    · intro h
      rw [h]
      exact Subgroup.mem_zpowers x
    · intro h
      apply le_antisymm hle
      exact Subgroup.zpowers_le_of_mem h
  rw [heq]
  -- Bézout の等式に基づく基本的な同値関係．
  -- x ∈ <x^k> ↔ gcd(k, ord(x)) = 1．
  rw [mem_zpowers_pow_iff, Nat.Coprime, Nat.gcd_comm k (orderOf x)]

/-- 位数 d の元 x が生成する巡回群の生成元の個数は φ(d)．
    Z/dZ の剰余類 k に x^k を対応させる全単射を直接構成する． -/
theorem card_generators_zpowers (x : H) :
    (generators H (Subgroup.zpowers x)).card = Nat.totient (orderOf x) := by
  classical
  -- Mathlib の φ は 0 ≤ k < d かつ gcd(d,k)=1 の個数．
  rw [Nat.totient_eq_card_coprime]
  symm
  -- k ↦ x^k による全単射．
  apply Finset.card_bij (fun k _ => x ^ k)
  · -- 写像が生成元集合に値を取る．
    intro k hk
    apply (mem_generators_iff H (Subgroup.zpowers x) (x ^ k)).mpr
    apply (pow_generates_iff_coprime H x k).mpr
    exact (Finset.mem_filter.mp hk).2
  · -- 0 ≤ i,j < ord(x) における単射性．
    intro i hi j hj hij
    have hi_lt : i < orderOf x := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hj_lt : j < orderOf x := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
    exact (pow_injOn_Iio_orderOf (x := x)) hi_lt hj_lt hij
  · -- 全射性：任意の生成元 y は x^k と書ける．
    intro y hy
    have hygen : Subgroup.zpowers y = Subgroup.zpowers x :=
      (mem_generators_iff H (Subgroup.zpowers x) y).mp hy
    have hymem : y ∈ Subgroup.zpowers x := by
      rw [← hygen]
      exact Subgroup.mem_zpowers y
    obtain ⟨k, hk, hky⟩ := Finset.mem_image.mp
      (mem_zpowers_iff_mem_range_orderOf.mp hymem)
    have hcop : (orderOf x).Coprime k := by
      apply (pow_generates_iff_coprime H x k).mp
      rw [hky]
      exact hygen
    exact ⟨k, Finset.mem_filter.mpr ⟨hk, hcop⟩, hky⟩

end Generators

/-! ## 有限群の元を位数ごとに分類する -/

section CountingByOrder

variable (H : Type*) [Group H] [Fintype H] [DecidableEq H]

/-- A_d：位数 d の元全体．orderOf が noncomputable なので，この定義も noncomputable とする． -/
noncomputable def elementsOfOrder (d : ℕ) : Finset H :=
  Finset.univ.filter (fun x : H => orderOf x = d)

@[simp]
theorem mem_elementsOfOrder (d : ℕ) (x : H) :
    x ∈ elementsOfOrder H d ↔ orderOf x = d := by
  simp [elementsOfOrder]

/-- A_d は H を被覆する（d は |H| の約数）． -/
theorem order_partition_union :
    ((Fintype.card H).divisors.biUnion (elementsOfOrder H)) = Finset.univ := by
  ext x
  constructor
  · intro _
    exact Finset.mem_univ x
  · intro _
    -- d := ord(x) とおけば，ラグランジュの定理より d | |H|．
    apply Finset.mem_biUnion.mpr
    refine ⟨orderOf x, ?_, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨orderOf_dvd_card, Fintype.card_ne_zero⟩
    · exact (mem_elementsOfOrder H (orderOf x) x).mpr rfl

/-- 異なる位数の元の集合は互いに素（共通の元を持たない）． -/
theorem order_partition_disjoint :
    (↑((Fintype.card H).divisors) : Set ℕ).PairwiseDisjoint
      (elementsOfOrder H) := by
  intro d hd e he hne
  apply Finset.disjoint_left.mpr
  intro x hxd hxe
  have hd' : orderOf x = d := (mem_elementsOfOrder H d x).mp hxd
  have he' : orderOf x = e := (mem_elementsOfOrder H e x).mp hxe
  exact hne (hd'.symm.trans he')

/-- 非交和の濃度を取ると |H| = Σ_{d | |H|} |A_d|． -/
theorem card_eq_sum_card_orderOf :
    Fintype.card H = ∑ d ∈ (Fintype.card H).divisors,
      (elementsOfOrder H d).card := by
  calc
    Fintype.card H = (Finset.univ : Finset H).card := Finset.card_univ.symm
    _ = ((Fintype.card H).divisors.biUnion (elementsOfOrder H)).card := by
      rw [order_partition_union H]
    _ = ∑ d ∈ (Fintype.card H).divisors, (elementsOfOrder H d).card := by
      exact Finset.card_biUnion (order_partition_disjoint H)

end CountingByOrder

/-! ## 補題1：Euler 関数の総和公式 -/

section Totient

variable (G : Type*) [Group G] [Fintype G] [DecidableEq G] [IsCyclic G]

/-- 位数 d の元全体 A_d と，一意な部分群 C_d の生成元集合 Φ_d は一致する． -/
theorem elementsOfOrder_eq_generators
    (d : ℕ) (hd : d ∣ Fintype.card G)
    (C : Subgroup G) (hC : Nat.card C = d) :
    elementsOfOrder G d = generators G C := by
  classical
  obtain ⟨C_d, hCd, hUnique⟩ := cyclic_subgroup_existsUnique G d hd
  ext y
  rw [mem_elementsOfOrder, mem_generators_iff]
  constructor
  · intro hy
    have hcard : Nat.card (Subgroup.zpowers y) = d := by
      rw [zpowers_card, hy]
    -- 位数 d の部分群はただ一つなので <y> = C_d = C．
    exact (hUnique (Subgroup.zpowers y) hcard).trans (hUnique C hC).symm
  · intro hy
    -- ord(y) = |<y>| = |C| = d．
    calc
      orderOf y = Nat.card (Subgroup.zpowers y) := (zpowers_card G y).symm
      _ = Nat.card C := by rw [hy]
      _ = d := hC

/-- 各 d | |G| について |A_d| = |Φ_d| = φ(d)． -/
theorem cyclic_card_orderOf_eq_totient
    (d : ℕ) (hd : d ∣ Fintype.card G) :
    (elementsOfOrder G d).card = Nat.totient d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have hgord : orderOf g = Fintype.card G := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card]
  let x := g ^ (Fintype.card G / d)
  let C_d := Subgroup.zpowers x
  have hx : orderOf x = d := orderOf_pow_div G g hgord d hd
  have hC : Nat.card C_d = d := by
    change Nat.card (Subgroup.zpowers x) = d
    rw [zpowers_card, hx]
  calc
    (elementsOfOrder G d).card = (generators G C_d).card := by
      rw [elementsOfOrder_eq_generators G d hd C_d hC]
    _ = Nat.totient (orderOf x) := card_generators_zpowers G x
    _ = Nat.totient d := by rw [hx]

/-- 補題1．n = Σ_{d | n} φ(d)．元の宣言との互換性のため n=0 も扱う． -/
theorem nat_eq_sum_totient_divisors (n : ℕ) :
    n = ∑ d ∈ n.divisors, Nat.totient d := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · letI : NeZero n := ⟨hn⟩
    -- Z/nZ を乗法記法で表す．群の演算は元の加法である．
    let G := Multiplicative (ZMod n)
    have hG : Fintype.card G = n := by
      -- 乗法記法の型 G と ZMod n の間には全単射がある．
      calc
        Fintype.card G = Fintype.card (ZMod n) := by
          exact Fintype.card_congr (Multiplicative.toAdd (α := ZMod n))
        _ = n := ZMod.card n
    calc
      n = Fintype.card G := hG.symm
      _ = ∑ d ∈ (Fintype.card G).divisors, (elementsOfOrder G d).card :=
        card_eq_sum_card_orderOf G
      _ = ∑ d ∈ (Fintype.card G).divisors, Nat.totient d := by
        apply Finset.sum_congr rfl
        intro d hd
        exact cyclic_card_orderOf_eq_totient G d (Nat.dvd_of_mem_divisors hd)
      _ = ∑ d ∈ n.divisors, Nat.totient d := by rw [hG]

end Totient

/-! ## 補題2：有限群が巡回群となるための判定 -/

section CyclicCriterion

variable (H : Type*) [Group H] [Fintype H] [DecidableEq H]

/-- S_d：d 乗して 1 になる元全体．一般には部分群とは限らない． -/
def rootsOfOne (d : ℕ) : Finset H :=
  Finset.univ.filter (fun x : H => x ^ d = 1)

@[simp]
theorem mem_rootsOfOne (d : ℕ) (x : H) :
    x ∈ rootsOfOne H d ↔ x ^ d = 1 := by
  simp [rootsOfOne]

/-- <x> の台集合を，0 以上 ord(x) 未満の自然数乗の像として列挙する．
    orderOf を用いるため noncomputable とする． -/
noncomputable def zpowersFinset (x : H) : Finset H :=
  (Finset.range (orderOf x)).image (fun k => x ^ k)

/-- 列挙した有限集合と部分群 <x> の所属条件は一致する． -/
theorem mem_zpowersFinset (x y : H) :
    y ∈ zpowersFinset H x ↔ y ∈ Subgroup.zpowers x := by
  exact mem_zpowers_iff_mem_range_orderOf.symm

/-- 列挙した有限集合の元の個数は ord(x) である． -/
theorem zpowersFinset_card (x : H) :
    (zpowersFinset H x).card = orderOf x := by
  calc
    (zpowersFinset H x).card = (Finset.range (orderOf x)).card := by
      unfold zpowersFinset
      apply Finset.card_image_of_injOn
      intro i hi j hj hij
      have hi_lt : i < orderOf x := Finset.mem_range.mp (Finset.mem_coe.mp hi)
      have hj_lt : j < orderOf x := Finset.mem_range.mp (Finset.mem_coe.mp hj)
      exact (pow_injOn_Iio_orderOf (x := x)) hi_lt hj_lt hij
    _ = orderOf x := Finset.card_range _

/-- 位数 d の元 x が存在し |S_d| ≤ d なら，S_d は <x> の台集合と一致する． -/
theorem roots_eq_zpowers
    (x : H) (d : ℕ) (hx : orderOf x = d)
    (hbound : (rootsOfOne H d).card ≤ d) :
    rootsOfOne H d = zpowersFinset H x := by
  let P : Finset H := zpowersFinset H x
  have hPcard : P.card = d := by
    -- 前節の部分体の位数の議論と同じく，台集合の濃度を比較する．
    change (zpowersFinset H x).card = d
    rw [zpowersFinset_card, hx]
  have hxd : x ^ d = 1 := by
    rw [← hx]
    exact pow_orderOf_eq_one x
  have hle : P ⊆ rootsOfOne H d := by
    intro y hy
    have hymem : y ∈ Subgroup.zpowers x := (mem_zpowersFinset H x y).mp hy
    apply (mem_rootsOfOne H d y).mpr
    exact pow_eq_one_of_mem_zpowers H x y d hxd hymem
  have hcard : (rootsOfOne H d).card ≤ P.card := by
    rw [hPcard]
    exact hbound
  -- <x> ⊆ S_d かつ |S_d| ≤ |<x>| より等しい．
  exact (Finset.eq_of_subset_of_card_le hle hcard).symm

/-- ord(y)=d と <y>=<x> は同値（ord(x)=d かつ根の個数の仮定の下）． -/
theorem orderOf_eq_iff_zpowers_eq_of_root_bound
    (x y : H) (d : ℕ) (hx : orderOf x = d)
    (hbound : (rootsOfOne H d).card ≤ d) :
    orderOf y = d ↔ Subgroup.zpowers y = Subgroup.zpowers x := by
  classical
  constructor
  · intro hy
    have hyd : y ^ d = 1 := by
      rw [← hy]
      exact pow_orderOf_eq_one y
    have hymem : y ∈ rootsOfOne H d := (mem_rootsOfOne H d y).mpr hyd
    rw [roots_eq_zpowers H x d hx hbound] at hymem
    have hyx : y ∈ Subgroup.zpowers x := (mem_zpowersFinset H x y).mp hymem
    have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := Subgroup.zpowers_le_of_mem hyx
    -- <y> ⊆ <x> かつ |<y>| = |<x>| = d．
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [zpowers_card H x, zpowers_card H y, hx, hy]
  · intro hy
    calc
      orderOf y = Nat.card (Subgroup.zpowers y) := (zpowers_card H y).symm
      _ = Nat.card (Subgroup.zpowers x) := by rw [hy]
      _ = orderOf x := zpowers_card H x
      _ = d := hx

/-- 位数 d の元が存在するなら，その個数は φ(d)． -/
theorem card_orderOf_eq_totient_of_root_bound
    (x : H) (d : ℕ) (hx : orderOf x = d)
    (hbound : (rootsOfOne H d).card ≤ d) :
    (elementsOfOrder H d).card = Nat.totient d := by
  classical
  have hsets : elementsOfOrder H d = generators H (Subgroup.zpowers x) := by
    ext y
    rw [mem_elementsOfOrder, mem_generators_iff]
    exact orderOf_eq_iff_zpowers_eq_of_root_bound H x y d hx hbound
  calc
    (elementsOfOrder H d).card = (generators H (Subgroup.zpowers x)).card := by rw [hsets]
    _ = Nat.totient (orderOf x) := card_generators_zpowers H x
    _ = Nat.totient d := by rw [hx]

/-- 補題2．有限群 H で各 d | |H| に対し x^d=1 の解が高々 d 個なら，H は巡回群． -/
theorem finiteGroup_isCyclic_of_root_bound_on_divisors
    (hroots : ∀ d : ℕ, d ∣ Fintype.card H → #{x : H | x ^ d = 1} ≤ d) :
    IsCyclic H := by
  let n := Fintype.card H
  let r (d : ℕ) := (elementsOfOrder H d).card
  have hn : 0 < n := Fintype.card_pos

  -- 【1】r_d = 0 または r_d = φ(d)．
  have hr (d : ℕ) (hd : d ∣ n) : r d = 0 ∨ r d = Nat.totient d := by
    by_cases h : r d = 0
    · exact Or.inl h
    · right
      have hpos : 0 < r d := Nat.pos_of_ne_zero h
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      have hxord : orderOf x = d := (mem_elementsOfOrder H d x).mp hx
      exact card_orderOf_eq_totient_of_root_bound H x d hxord (hroots d hd)

  have hle : ∀ d ∈ n.divisors, r d ≤ Nat.totient d := by
    intro d hd
    rcases hr d (Nat.dvd_of_mem_divisors hd) with hz | heq
    · rw [hz]
      exact Nat.zero_le _
    · exact heq.le

  -- 【2】H を位数で分類すると n = Σ r_d．補題1から n = Σ φ(d)．
  have hsum : (∑ d ∈ n.divisors, r d) = ∑ d ∈ n.divisors, Nat.totient d := by
    calc
      (∑ d ∈ n.divisors, r d) = n := (card_eq_sum_card_orderOf H).symm
      _ = ∑ d ∈ n.divisors, Nat.totient d := nat_eq_sum_totient_divisors n

  -- 【3】もし r_d=0 なら，φ(d)>0 なので総和が小さくなり矛盾する．
  have hrpos : ∀ d ∈ n.divisors, 0 < r d := by
    intro d hd
    by_contra h
    have hz : r d = 0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd) hn
    have hlt : r d < Nat.totient d := by
      rw [hz]
      exact Nat.totient_pos.mpr hdpos
    have hsumlt : (∑ e ∈ n.divisors, r e) < ∑ e ∈ n.divisors, Nat.totient e := by
      exact Finset.sum_lt_sum hle ⟨d, hd, hlt⟩
    exact (ne_of_lt hsumlt) hsum

  -- 【4】各 d | n で r_d = φ(d) > 0．特に d=n．
  have hnn : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hn.ne'⟩
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (hrpos n hnn)
  have hxord : orderOf x = n := (mem_elementsOfOrder H n x).mp hx

  -- ord(x)=n だから |<x>|=|H|．よって H=<x>．
  apply isCyclic_iff_exists_zpowers_eq_top.mpr
  refine ⟨x, ?_⟩
  exact zpowers_eq_top_of_orderOf_eq_card H x hxord

end CyclicCriterion

/-! ## 定理2：有限体の乗法群 -/

section FiniteFieldMultiplicativeGroup

variable (K : Type*) [Field K] [Fintype K]

/-- x^d=1 と x が多項式 X^d-1 の根であることは同値．
    S1.1.1 の mem_frobeniusFixedSubfield_iff_isRoot と同様の議論． -/
theorem pow_eq_one_iff_isRoot (d : ℕ) (x : K) :
    x ^ d = 1 ↔ Polynomial.IsRoot (Polynomial.X ^ d - 1 : Polynomial K) x := by
  change x ^ d = 1 ↔ Polynomial.eval x (Polynomial.X ^ d - 1 : Polynomial K) = 0
  rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one]
  constructor
  · intro hx
    exact sub_eq_zero.mpr hx
  · intro hx
    exact sub_eq_zero.mp hx

/-- d>0 ならば X^d-1 の次数は d である．
    S1.1.1 の frobeniusPolynomial_natDegree と同じ次数の比較を行う． -/
theorem X_pow_sub_one_natDegree (d : ℕ) (hd : 0 < d) :
    (Polynomial.X ^ d - 1 : Polynomial K).natDegree = d := by
  calc
    (Polynomial.X ^ d - 1 : Polynomial K).natDegree
        = (Polynomial.X ^ d : Polynomial K).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      rw [Polynomial.natDegree_one, Polynomial.natDegree_X_pow]
      exact hd
    _ = d := Polynomial.natDegree_X_pow d

/-- d>0 ならば X^d-1 は零多項式ではない． -/
theorem X_pow_sub_one_ne_zero (d : ℕ) (hd : 0 < d) :
    (Polynomial.X ^ d - 1 : Polynomial K) ≠ 0 := by
  intro hz
  have hdeg := X_pow_sub_one_natDegree K d hd
  rw [hz, Polynomial.natDegree_zero] at hdeg
  exact (ne_of_gt hd) hdeg.symm

-- 定理の主張を解釈する段階から古典論理を使えるようにする．
open scoped Classical in
/-- Kˣ の元で x^d=1 を満たすものは高々 d 個． -/
theorem units_root_bound (d : ℕ) (hd : 0 < d) :
    #{x : Kˣ | x ^ d = 1} ≤ d := by
  let P : Polynomial K := Polynomial.X ^ d - 1
  have hPne : P ≠ 0 := X_pow_sub_one_ne_zero K d hd
  have hPdeg : P.natDegree = d := X_pow_sub_one_natDegree K d hd
  calc
    #{x : Kˣ | x ^ d = 1} ≤ P.roots.toFinset.card := by
      -- Kˣ → K の単射 u ↦ u.val を使う．
      apply Finset.card_le_card_of_injOn (fun u : Kˣ => (u : K))
      · -- 単元 u は P の根に写る．
        intro u hu
        have huPow : u ^ d = 1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
        have huK : (u : K) ^ d = 1 := by
          simpa only [Units.val_pow_eq_pow_val, Units.val_one] using
            congrArg (fun v : Kˣ => (v : K)) huPow
        change u.val ∈ P.roots.toFinset
        apply Multiset.mem_toFinset.mpr
        apply (Polynomial.mem_roots hPne).mpr
        exact (pow_eq_one_iff_isRoot K d (u : K)).mp huK
      · -- u ↦ u.val は単射．
        intro u hu v hv huv
        exact Units.val_injective huv
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = d := hPdeg

open scoped Classical in
/-- 有限体 K の乗法群 Kˣ は巡回群である． -/
theorem finiteField_units_isCyclic : IsCyclic Kˣ := by
  -- 補題2を H=Kˣ に適用する．
  apply finiteGroup_isCyclic_of_root_bound_on_divisors (H := Kˣ)
  intro d hdvd
  have hn : 0 < Fintype.card Kˣ := Fintype.card_pos
  have hd : 0 < d := Nat.pos_of_dvd_of_pos hdvd hn
  exact units_root_bound K d hd

/-- |Kˣ| = |K|-1．S1.1.1 の subfield_le_frobeniusFixedSubfield の中でも
    用いた単元の個数の公式を，ここで独立した定理にする． -/
theorem finiteField_units_card : Nat.card Kˣ = Fintype.card K - 1 := by
  calc
    Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
    _ = Fintype.card K - 1 := by rw [Nat.card_eq_fintype_card]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

local instance : Algebra (ZMod p) K := ZMod.algebra K p

/-- 定理2．標数 p，ZMod p 上 f 次元の有限体 K の乗法群は
    位数 p^f-1 の巡回群である．元の定理の型を維持する． -/
theorem finiteField_multiplicativeGroup_cyclic
    (f : ℕ) (hfinrank : Module.finrank (ZMod p) K = f) :
    IsCyclic Kˣ ∧ Nat.card Kˣ = p ^ f - 1 := by
  constructor
  · -- 巡回性：補題2と多項式の根の個数から示した結果．
    exact finiteField_units_isCyclic K
  · -- 位数：前節の定理1 (i) を利用する．
    calc
      Nat.card Kˣ = Fintype.card K - 1 := finiteField_units_card K
      _ = p ^ f - 1 := by rw [finiteField_card_eq_pow K p f hfinrank]

end FiniteFieldMultiplicativeGroup

/-! ## 前節の結果を組み合わせた系 -/

/-- 任意の有限体 K に対し，ある素数 p と正の整数 f が存在し，
    |K|=p^f かつ乗法群 Kˣ は位数 p^f-1 の巡回群となる． -/
theorem finiteField_units_prime_pow_card
    (K : Type*) [Field K] [Fintype K] :
    ∃ p f : ℕ, Nat.Prime p ∧ 0 < f ∧ Fintype.card K = p ^ f ∧
      IsCyclic Kˣ ∧ Nat.card Kˣ = p ^ f - 1 := by
  let p := ringChar K
  letI : CharP K p := ringChar.charP K
  -- 前節の定理1：有限体の標数は素数．
  have hp : Nat.Prime p := finiteField_char_is_prime K p
  letI : Fact p.Prime := ⟨hp⟩
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  let f := Module.finrank (ZMod p) K
  -- 前節の定理1：有限体の位数は標数の冪．
  have hcard : Fintype.card K = p ^ f := finiteField_card_eq_pow_finrank K p
  -- 前節で証明済み：体には 0 と 1 があるので指数は 0 ではない．
  have hf : f ≠ 0 := finiteField_pow_exponent_ne_zero K p f hcard
  have hcyc := finiteField_multiplicativeGroup_cyclic K p f rfl
  exact ⟨p, f, hp, Nat.pos_of_ne_zero hf, hcard, hcyc.1, hcyc.2⟩

end SerreNumberTheory
