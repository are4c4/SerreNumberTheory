import Mathlib

namespace SerreNumberTheory

/-!
# 体の標数
-/

section Characteristic

variable (K : Type*) [Field K] -- Kを体とする．
variable (p : ℕ) [CharP K p] -- pをKの標数とする．

include K in -- `include` : 指定した変数を定理に含める
/--
体の標数は素数または `0` である．
-/
theorem field_char_is_prime_or_zero :
    Nat.Prime p ∨ p = 0 := by
  exact CharP.char_is_prime_or_zero K p

end Characteristic

/-!
# Frobenius写像
-/

section Frobenius

variable (K : Type*) [Field K]
variable (p : ℕ) [Fact p.Prime] [CharP K p] -- `K` の標数は素数`p`


/-! ## `p`乗写像 -/

section PowerMap

/--
`p`乗写像（Frobenius写像）を通常の関数として定義する．
-/
def myFrobeniusFun : K → K :=
  fun x ↦ x ^ p

/--
`p`乗写像は `0` を `0` に送る．
-/
theorem myFrobeniusFun_zero :
    myFrobeniusFun K p 0 = 0 := by
  unfold myFrobeniusFun                 -- `myFrobeniusFun`の定義を展開
  exact zero_pow (expChar_ne_zero K p)  -- `p` が `0` でないとき，`0^p = 0`

omit [Fact p.Prime] [CharP K p] in -- `omit` : 指定した変数を定理から外す
/--
`p`乗写像は `1` を `1` に送る．
-/
theorem myFrobeniusFun_one :
    myFrobeniusFun K p 1 = 1 := by
  unfold myFrobeniusFun
  exact one_pow p

omit [Fact p.Prime] [CharP K p] in
/--
`p`乗写像は乗法を保つ．
-/
theorem myFrobeniusFun_mul (x y : K) :
    myFrobeniusFun K p (x * y) = myFrobeniusFun K p x * myFrobeniusFun K p y := by
  unfold myFrobeniusFun
  exact mul_pow x y p

/--
標数 `p` では，`p`乗写像は加法を保つ．
-/
theorem myFrobeniusFun_add (x y : K) :
    myFrobeniusFun K p (x + y) = myFrobeniusFun K p x + myFrobeniusFun K p y := by
  unfold myFrobeniusFun
  exact add_pow_expChar x y p

end PowerMap


/-! ## Frobenius環準同型 -/

section RingHom

/--
`x ↦ x ^ p`で与えられるFrobenius環準同型．
（写像`myFrobeniusFun`を準同型として定義し直す）
-/
def myFrobenius : K →+* K where -- `→+*` : 準同型（加法`+`と乗法`*`を保つ）
  toFun := myFrobeniusFun K p

  map_zero' := by
    exact myFrobeniusFun_zero K p

  map_one' := by
    exact myFrobeniusFun_one K p

  map_add' := by
    intro x y
    exact myFrobeniusFun_add K p x y

  map_mul' := by
    intro x y
    exact myFrobeniusFun_mul K p x y

/--
自作したFrobenius環準同型の値は `x ^ p` である．
（`myFrobenius K p x = x ^ p`を`simp`で使えるようにする）
-/
@[simp]
theorem myFrobenius_apply (x : K) :
    myFrobenius K p x = x ^ p := by
  rfl

/--
自作したFrobenius環準同型は，
Mathlibの`frobenius`と一致する．
-/
theorem myFrobenius_eq_frobenius :
    myFrobenius K p = frobenius K p := by
  apply RingHom.ext
  intro x
  rw [myFrobenius_apply, frobenius_def]

/--
体から体への環準同型は単射である．
（Mathlibの`RingHom.injective` を体の場合に特殊化したもの）
-/
theorem fieldRingHom_injective
    {K L : Type*} [Field K] [Field L]
    (f : K →+* L) :
    Function.Injective f := by
  exact f.injective

/--
自作したFrobenius環準同型は単射である．
-/
theorem myFrobenius_injective :
    Function.Injective (myFrobenius K p) := by -- InfoViewの`⇑`は環準同型`K →+* K`を写像`K → K`とみるという意味
  exact fieldRingHom_injective (myFrobenius K p)

end RingHom

/-! ## Frobenius写像の像との同型 -/

section Equivalence

/--
自作したFrobenius写像の像を部分体`K^p`として取り，
その元からなる型に名前をつけている．
-/
abbrev MyFrobeniusPowers : Type _ := -- `abbrev` : 長い型や式に、読みやすい短い名前をつける
  (myFrobenius K p).fieldRange

/--
Frobenius写像の終域を、その像 `K^p` に制限する．
-/
def myFrobeniusToPowers :
    K →+* MyFrobeniusPowers K p :=
  (myFrobenius K p).rangeRestrictField

/--
像に終域を制限したFrobenius写像は全単射である．
-/
theorem myFrobeniusToPowers_bijective :
    Function.Bijective (myFrobeniusToPowers K p) := by
  constructor

  · -- 単射性
    intro x y hxy
    apply myFrobenius_injective K p
    exact congrArg Subtype.val hxy

  · -- 全射性
    intro z
    rcases z with ⟨zValue, hz⟩
    rcases hz with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

/--
Frobenius写像`K → K^p`は環同型．
-/
noncomputable def myFrobeniusEquivPowers :
    K ≃+* MyFrobeniusPowers K p := by
  apply RingEquiv.ofBijective (myFrobeniusToPowers K p)
  exact myFrobeniusToPowers_bijective K p

end Equivalence

end Frobenius

/-!
# 有限体の位数
-/

section FiniteFieldCardinality

/--
（S010101定理1前半）
有限体の標数は素数である．
-/
theorem finiteField_char_is_prime
    (K : Type*) [Field K] [Fintype K]
    (p : ℕ) [CharP K p] :
    Nat.Prime p := by
  rcases field_char_is_prime_or_zero K p with hp | hp
  · -- p=素数
    exact hp
  · -- p=0
    have hp_ne_zero : p ≠ 0 := by -- 矛盾を導いて示す
      exact CharP.char_ne_zero_of_finite K p
    have hFalse : False := by
      apply hp_ne_zero
      exact hp
    exact hFalse.elim

variable (K : Type*) [Field K] [Fintype K] -- `K`は有限体
variable (p : ℕ) [Fact p.Prime] [CharP K p] --有限体`K`の標数は素数`p`

/--
標数 `p` の有限体 `K` に標準的な `ZMod p`-代数構造を入れる．
（`K` を `ZMod p` 上の多元環とする．）
これにより `K` を `ZMod p` 上のベクトル空間として扱える．
-/
local instance : Algebra (ZMod p) K :=
  ZMod.algebra K p

/--
標数`p`の有限体`K`の位数は，
`ZMod p`上の次元を指数とする`p`の冪である．
-/
theorem finiteField_card_eq_pow_finrank :
    Fintype.card K = -- Fintype : 有限個の元を持つ型
      p ^ Module.finrank (ZMod p) K := by

  -- `ZMod p`上の`K`の基底を選ぶ
  let b := Module.finBasis (ZMod p) K

  calc
    -- `K`の元は基底に関する係数の組と一対一に対応する
    Fintype.card K
      = Fintype.card (Fin (Module.finrank (ZMod p) K) → ZMod p) := by
        -- (Fin (Module.finrank (ZMod p) K) → ZMod p) : 関数全体の集合
      exact Fintype.card_congr b.equivFun.toEquiv
        -- Fintype.card_congr : 全単射があれば濃度が等しい
        -- b.equivFun : 基底bから(ZMod p)への線形同型
        -- toEquiv : 線形同型を単なる全単射として扱う

    -- n 個の係数があり，各係数には |ZMod p| 通りの選択肢がある
    _ = Fintype.card (ZMod p) ^ Module.finrank (ZMod p) K := by
      exact Fintype.card_pi_const (ZMod p) (Module.finrank (ZMod p) K)

    -- ZMod p の位数は p
    _ = p ^ Module.finrank (ZMod p) K := by
      rw [ZMod.card]

/--
（S010101定理1後半）
`K`が`ZMod p`上`f`次元ならば，`K`の位数は`p ^ f`である．
（finiteField_card_eq_pow_finrankの結果をModule.finrank (ZMod p) K = fで書き換えている．）
-/
theorem finiteField_card_eq_pow
    (f : ℕ)
    (hfinrank : Module.finrank (ZMod p) K = f) :
      -- Module.finrank (ZMod p) K = f となるように f : ℕ を取る．
    Fintype.card K = p ^ f := by
  rw [
    finiteField_card_eq_pow_finrank K p,
      -- finiteField_card_eq_pow_finrank の結果を適応
    hfinrank
      -- 仮定より，Module.finrank (ZMod p) K = f を適応
  ]

end FiniteFieldCardinality

/-!
# 代数閉体内の有限部分体
-/

section FiniteSubfieldInAlgebraicClosure

variable (Ω : Type*) [Field Ω]
variable (p f : ℕ) [Fact p.Prime] [CharP Ω p]

/--
標数`p`の体`Ω`において，
`x ^ (p ^ f) = x`を満たす元全体がなす部分体．
-/
def frobeniusFixedSubfield : Subfield Ω where
  carrier :=
    {x : Ω | (iterateFrobenius Ω p f) x = x}

  zero_mem' := by
    change (iterateFrobenius Ω p f) 0 = 0
    exact (iterateFrobenius Ω p f).map_zero

  one_mem' := by
    change (iterateFrobenius Ω p f) 1 = 1
    exact (iterateFrobenius Ω p f).map_one

  add_mem' := by
    intro x y hx hy
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) y = y at hy
    change (iterateFrobenius Ω p f) (x + y) = x + y
    rw [(iterateFrobenius Ω p f).map_add, hx, hy]

  mul_mem' := by
    intro x y hx hy
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) y = y at hy
    change (iterateFrobenius Ω p f) (x * y) = x * y
    rw [(iterateFrobenius Ω p f).map_mul, hx, hy]

  neg_mem' := by
    intro x hx
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) (-x) = -x
    rw [(iterateFrobenius Ω p f).map_neg, hx]

  inv_mem' := by
    intro x hx
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) x⁻¹ = x⁻¹
    rw [iterateFrobenius_def] at hx ⊢
    rw [inv_pow, hx]

/--
`x`が`frobeniusFixedSubfield Ω p f`に属することと，
`x ^ (p ^ f) = x`であることは同値である．
-/
@[simp]
theorem mem_frobeniusFixedSubfield_iff
    (x : Ω) :
    x ∈ frobeniusFixedSubfield Ω p f ↔
      x ^ (p ^ f) = x := by
  change
    (iterateFrobenius Ω p f) x = x ↔
      x ^ (p ^ f) = x
  rw [iterateFrobenius_def]

/--
`x`が`frobeniusFixedSubfield Ω p f`に属することと，
`X ^ (p ^ f) - X`の根であることは同値である．
-/
theorem mem_frobeniusFixedSubfield_iff_isRoot
    (x : Ω) :
    x ∈ frobeniusFixedSubfield Ω p f ↔
      Polynomial.IsRoot
        (Polynomial.X ^ (p ^ f) - Polynomial.X)
        x := by
  rw [mem_frobeniusFixedSubfield_iff]

  change
    x ^ (p ^ f) = x ↔
      Polynomial.eval x
        (Polynomial.X ^ (p ^ f) - Polynomial.X) = 0

  rw [
    Polynomial.eval_sub,
    Polynomial.eval_pow,
    Polynomial.eval_X
  ]

  constructor
  · intro hx
    exact sub_eq_zero.mpr hx
  · intro hx
    exact sub_eq_zero.mp hx

omit [Fact p.Prime] [CharP Ω p] in
/--
代数閉体`Ω`上で，
`X ^ (p ^ f) - X`は完全に分解する．
-/
theorem frobeniusPolynomial_splits
    [IsAlgClosed Ω] :
    (Polynomial.X ^ (p ^ f) - Polynomial.X :
      Polynomial Ω).Splits := by
  exact IsAlgClosed.splits _

omit [Fact p.Prime] in
/--
標数 `p` の体 `Ω` において，
`X ^ (p ^ f) - X` の形式的微分は `-1` である．
-/
theorem frobeniusPolynomial_derivative
    (hf : f ≠ 0) :
    (Polynomial.X ^ (p ^ f) - Polynomial.X :
      Polynomial Ω).derivative = -1 := by

  -- 標数 p では，p ^ f が 0 になる
  have hcoeff : ((p ^ f : ℕ) : Ω) = 0 := by
    apply (CharP.cast_eq_zero_iff Ω p (p ^ f)).mpr
    exact dvd_pow_self p hf

  -- 微分の公式を適用する
  rw [
    Polynomial.derivative_sub,
    Polynomial.derivative_X_pow,
    Polynomial.derivative_X
  ]

  -- p ^ f = 0 を代入して整理する
  simp [hcoeff]

omit [Fact p.Prime] in
/--
標数 `p` において，
`X ^ (p ^ f) - X` は分離多項式である．
-/
theorem frobeniusPolynomial_separable
    (hf : f ≠ 0) :
    (Polynomial.X ^ (p ^ f) - Polynomial.X :
      Polynomial Ω).Separable := by

  -- 分離性を，多項式とその導関数が互いに素であることに言い換える
  rw [
    Polynomial.separable_def,
    frobeniusPolynomial_derivative Ω p f hf
  ]

  -- 任意の多項式と -1 は互いに素
  exact isCoprime_one_right.neg_right

omit [CharP Ω p] in
/--
`f ≠ 0`ならば，
`X ^ (p ^ f) - X`の次数は`p ^ f`である．
-/
theorem frobeniusPolynomial_natDegree
    (hf : f ≠ 0) :
    (Polynomial.X ^ (p ^ f) - Polynomial.X :
      Polynomial Ω).natDegree = p ^ f := by
  have hp_one_lt : 1 < p :=
    (Fact.out : Nat.Prime p).one_lt

  have hpow_one_lt : 1 < p ^ f := by
    exact Nat.one_lt_pow hf hp_one_lt

  calc
    (Polynomial.X ^ (p ^ f) - Polynomial.X :
        Polynomial Ω).natDegree
        =
        (Polynomial.X ^ (p ^ f) :
          Polynomial Ω).natDegree := by
      apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
      simpa using hpow_one_lt

    _ = p ^ f := by
      exact Polynomial.natDegree_X_pow (p ^ f)

/--
代数閉体`Ω`において，
`X ^ (p ^ f) - X`の異なる根の個数は`p ^ f`である．
-/
theorem frobeniusPolynomial_rootSet_card
    [IsAlgClosed Ω]
    (hf : f ≠ 0) :
    Fintype.card
      ↑((Polynomial.X ^ (p ^ f) - Polynomial.X :
          Polynomial Ω).rootSet Ω)
      = p ^ f := by
  calc
    Fintype.card
        ↑((Polynomial.X ^ (p ^ f) - Polynomial.X :
            Polynomial Ω).rootSet Ω)
        =
        (Polynomial.X ^ (p ^ f) - Polynomial.X :
          Polynomial Ω).natDegree := by
      apply Polynomial.card_rootSet_eq_natDegree
      · exact frobeniusPolynomial_separable Ω p f hf
      · simpa using frobeniusPolynomial_splits Ω p f
    _ = p ^ f :=
      frobeniusPolynomial_natDegree Ω p f hf

/--
`frobeniusFixedSubfield Ω p f`の台集合は，
`X ^ (p ^ f) - X`の根集合と一致する．
-/
theorem frobeniusFixedSubfield_carrier_eq_rootSet
    (hf : f ≠ 0) :
    (frobeniusFixedSubfield Ω p f : Set Ω)
      =
    ↑((Polynomial.X ^ (p ^ f) - Polynomial.X :
        Polynomial Ω).rootSet Ω) := by
  let P : Polynomial Ω :=
    Polynomial.X ^ (p ^ f) - Polynomial.X

  have hP_ne : P ≠ 0 := by
    simpa [P] using
      (frobeniusPolynomial_separable Ω p f hf).ne_zero

  ext x

  change
    (x ∈ frobeniusFixedSubfield Ω p f) ↔
      x ∈ P.rootSet Ω

  rw [Polynomial.mem_rootSet_of_ne hP_ne]

  simpa [P, Polynomial.IsRoot] using
    (mem_frobeniusFixedSubfield_iff_isRoot Ω p f x)

/--
代数閉体`Ω`の部分体`frobeniusFixedSubfield Ω p f`は，
`p ^ f`個の元を持つ．
-/
theorem frobeniusFixedSubfield_natCard
    [IsAlgClosed Ω]
    (hf : f ≠ 0) :
    Nat.card (frobeniusFixedSubfield Ω p f) = p ^ f := by
  let P : Polynomial Ω :=
    Polynomial.X ^ (p ^ f) - Polynomial.X

  let e :
      frobeniusFixedSubfield Ω p f
        ≃
      ↑(P.rootSet Ω) := by
    exact Equiv.setCongr
      (frobeniusFixedSubfield_carrier_eq_rootSet Ω p f hf)

  calc
    Nat.card (frobeniusFixedSubfield Ω p f)
        =
        Nat.card ↑(P.rootSet Ω) := by
      exact Nat.card_congr e

    _ = Fintype.card ↑(P.rootSet Ω) := by
      exact Nat.card_eq_fintype_card

    _ = p ^ f := by
      simpa [P] using
        frobeniusPolynomial_rootSet_card Ω p f hf


/--
`p ^ f`個の元を持つ`Ω`の有限部分体は，
`frobeniusFixedSubfield Ω p f`に含まれる．
-/
theorem subfield_le_frobeniusFixedSubfield
    (L : Subfield Ω)
    [Fintype L]
    (hcard : Fintype.card L = p ^ f) :
    L ≤ frobeniusFixedSubfield Ω p f := by
  intro x hx

  rw [mem_frobeniusFixedSubfield_iff]

  let y : L := ⟨x, hx⟩

  have hy :
      y ^ Fintype.card L = y := by

    -- 場合①：y = 0
    by_cases hy0 : y = 0

    · rw [hy0]
      exact zero_pow Fintype.card_ne_zero

    -- 場合②：y ≠ 0
    · -- ラグランジュの定理より y ^ (|L| - 1) = 1
      have hy_order :
          y ^ (Fintype.card L - 1) = 1 := by
        calc
          y ^ (Fintype.card L - 1)
              =
              (Units.mk0 y hy0 ^
                (Fintype.card L - 1) : Lˣ).1 := by
                  rw [Units.val_pow_eq_pow_val, Units.val_mk0]

          _ = 1 := by
                classical
                rw [← Fintype.card_units, pow_card_eq_one]
                rfl

      -- y ^ |L| = y ^ (|L| - 1) * y = y
      rw [
        ← Nat.succ_pred_eq_of_pos Fintype.card_pos,
        pow_succ,
        Nat.pred_eq_sub_one,
        hy_order,
        one_mul
      ]

  have hyΩ :
      (y : Ω) ^ Fintype.card L = (y : Ω) := by
    exact congrArg ((↑) : L → Ω) hy

  simpa [y, hcard] using hyΩ

/--
代数閉体`Ω`において，`p ^ f`個の元を持つ部分体は，
`frobeniusFixedSubfield Ω p f`に等しい．
-/
theorem subfield_eq_frobeniusFixedSubfield
    [IsAlgClosed Ω]
    (L : Subfield Ω)
    [Fintype L]
    (hf : f ≠ 0)
    (hcard : Fintype.card L = p ^ f) :
    L = frobeniusFixedSubfield Ω p f := by
  apply SetLike.coe_injective

  apply Set.Finite.eq_of_subset_of_card_le

  · rw [
      frobeniusFixedSubfield_carrier_eq_rootSet
        Ω p f hf
    ]

    exact
      (Polynomial.X ^ (p ^ f) - Polynomial.X :
        Polynomial Ω).rootSet_finite Ω

  · exact
      subfield_le_frobeniusFixedSubfield
        Ω p f L hcard

  · change
      Nat.card (frobeniusFixedSubfield Ω p f) ≤
        Nat.card L

    rw [
      frobeniusFixedSubfield_natCard Ω p f hf,
      Nat.card_eq_fintype_card,
      hcard
    ]

/--
代数閉体`Ω`の中には，`p ^ f`個の元を持つ部分体が一意に存在する．
その部分体は`frobeniusFixedSubfield Ω p f`である．
-/
theorem existsUnique_subfield_natCard_eq_pow
    [IsAlgClosed Ω]
    (hf : f ≠ 0) :
    ∃! L : Subfield Ω,
      Nat.card L = p ^ f := by
  refine
    ⟨frobeniusFixedSubfield Ω p f,
      frobeniusFixedSubfield_natCard Ω p f hf,
      ?_⟩

  intro L hL

  have hpow_pos : 0 < p ^ f := by
    exact pow_pos (Fact.out : Nat.Prime p).pos f

  have hL_ne : Nat.card L ≠ 0 := by
    rw [hL]
    exact ne_of_gt hpow_pos

  letI : Finite L :=
    Nat.finite_of_card_ne_zero hL_ne

  letI : Fintype L :=
    Fintype.ofFinite L

  have hcard :
      Fintype.card L = p ^ f := by
    rw [← Nat.card_eq_fintype_card]
    exact hL

  exact
    subfield_eq_frobeniusFixedSubfield
      Ω p f L hf hcard

end FiniteSubfieldInAlgebraicClosure

/-!
# 有限体の一意性
-/

section FiniteFieldUniqueness

variable (K : Type*) [Field K] [Fintype K]
variable (p f : ℕ) [Fact p.Prime] [CharP K p]

local instance : Algebra (ZMod p) K :=
  ZMod.algebra K p

/--
標数 `p` の有限体 `K` を，
`ZMod p` の代数閉包に埋め込む．
-/
noncomputable def finiteFieldEmbeddingIntoClosure :
    K →ₐ[ZMod p] AlgebraicClosure (ZMod p) := by

  -- 有限次元拡大は代数拡大である
  letI : Algebra.IsAlgebraic (ZMod p) K :=
    Algebra.IsAlgebraic.of_finite (ZMod p) K

  -- 代数拡大から代数閉体への埋め込み
  exact IsAlgClosed.lift

/--
有限体 `K` を `ZMod p` の代数閉包に埋め込んだときの像．
-/
noncomputable def finiteFieldImageInClosure :
    Subfield (AlgebraicClosure (ZMod p)) :=
  (finiteFieldEmbeddingIntoClosure K p).toRingHom.fieldRange

/--
`K` を代数閉包に埋め込んだ像の位数は，
元の有限体 `K` の位数 `p ^ f` に等しい．
-/
theorem finiteFieldImageInClosure_natCard
    (hcard : Fintype.card K = p ^ f) :
    Nat.card (finiteFieldImageInClosure K p) = p ^ f := by

  let φ : K →+* AlgebraicClosure (ZMod p) :=
    (finiteFieldEmbeddingIntoClosure K p).toRingHom

  calc
    Nat.card (finiteFieldImageInClosure K p)
        = Nat.card φ.fieldRange := by
            rfl

    _ = Nat.card K := by
          exact Nat.card_congr
            (φ.rangeRestrictFieldEquiv.symm.toEquiv)

    _ = Fintype.card K := by
          exact Nat.card_eq_fintype_card

    _ = p ^ f := by
          exact hcard

/--
位数 `p ^ f` の有限体 `K` を代数閉包に埋め込むと，
その像は `frobeniusFixedSubfield` と一致する．
-/
theorem finiteFieldImage_eq_frobeniusFixedSubfield
    (hf : f ≠ 0)
    (hcard : Fintype.card K = p ^ f) :
    finiteFieldImageInClosure K p =
      frobeniusFixedSubfield
        (AlgebraicClosure (ZMod p)) p f := by

  -- 定理1 (ii)：位数 p ^ f の部分体は一意に存在する
  obtain ⟨L, _, hUnique⟩ :=
    existsUnique_subfield_natCard_eq_pow
      (AlgebraicClosure (ZMod p)) p f hf

  -- 埋め込んだ像の位数は p ^ f
  have hImage :
      Nat.card (finiteFieldImageInClosure K p) = p ^ f := by
    exact finiteFieldImageInClosure_natCard K p f hcard

  -- Frobenius固定部分体の位数も p ^ f
  have hFixed :
      Nat.card
        (frobeniusFixedSubfield
          (AlgebraicClosure (ZMod p)) p f) = p ^ f := by
    exact frobeniusFixedSubfield_natCard
      (AlgebraicClosure (ZMod p)) p f hf

  -- 一意性から両者は等しい
  calc
    finiteFieldImageInClosure K p
        = L := by
          exact hUnique _ hImage

    _ = frobeniusFixedSubfield
          (AlgebraicClosure (ZMod p)) p f := by
          exact (hUnique _ hFixed).symm

/--
位数が `p ^ f` の有限体 `K` は，
代数閉包内の `frobeniusFixedSubfield` と環同型である．
-/
noncomputable def finiteFieldRingEquivFixedSubfield
    (hf : f ≠ 0)
    (hcard : Fintype.card K = p ^ f) :
    K ≃+* frobeniusFixedSubfield
      (AlgebraicClosure (ZMod p)) p f := by

  -- K から代数閉包への環準同型
  let φ : K →+* AlgebraicClosure (ZMod p) :=
    (finiteFieldEmbeddingIntoClosure K p).toRingHom

  -- その像は Frobenius 固定部分体に等しい
  have hImage :
      φ.fieldRange =
        frobeniusFixedSubfield
          (AlgebraicClosure (ZMod p)) p f := by
    exact finiteFieldImage_eq_frobeniusFixedSubfield
      K p f hf hcard

  -- K ≃ φ(K) と φ(K) = F_q を組み合わせる
  exact
    φ.rangeRestrictFieldEquiv.trans
      (RingEquiv.subfieldCongr hImage)

omit [Fact (Nat.Prime p)] [CharP K p] in
/--
位数が `p ^ f` である有限体では，
指数 `f` は `0` ではない．
-/
theorem finiteField_pow_exponent_ne_zero
    (hcard : Fintype.card K = p ^ f) :
    f ≠ 0 := by

  intro hf

  -- f = 0 ならば，K の位数は高々 1
  have hcard_le_one : Fintype.card K ≤ 1 := by
    simpa [hf] using hcard.le

  -- しかし，体には 0 と 1 という異なる元が存在する
  have hsub : Subsingleton K :=
    Fintype.card_le_one_iff_subsingleton.mp hcard_le_one

  exact not_subsingleton K hsub


/--
標数 `p` で，ともに `p ^ f` 個の元を持つ
2つの有限体 `K`, `L` は環同型である．
-/
noncomputable def finiteFieldsRingEquiv
    (L : Type*) [Field L] [Fintype L] [CharP L p]
    (hK : Fintype.card K = p ^ f)
    (hL : Fintype.card L = p ^ f) :
    K ≃+* L := by

  -- L に ZMod p 上の代数構造を入れる
  letI : Algebra (ZMod p) L :=
    ZMod.algebra L p

  -- 位数の仮定から f ≠ 0 を導く
  have hf : f ≠ 0 :=
    finiteField_pow_exponent_ne_zero K p f hK

  -- 両者を同じ Frobenius 固定部分体に同型で写す
  exact
    (finiteFieldRingEquivFixedSubfield K p f hf hK).trans
      (finiteFieldRingEquivFixedSubfield L p f hf hL).symm

end FiniteFieldUniqueness


/--
同じ位数を持つ2つの有限体は環同型である．
-/
noncomputable def finiteFieldsRingEquiv_of_card_eq
    (K L : Type*)
    [Field K] [Fintype K]
    [Field L] [Fintype L]
    (hcard : Fintype.card K = Fintype.card L) :
    K ≃+* L := by

  -- K の標数を p とする
  let p : ℕ := ringChar K
  letI : CharP K p := ringChar.charP K

  -- 有限体の標数 p は素数
  have hp : Nat.Prime p :=
    finiteField_char_is_prime K p

  letI : Fact p.Prime := ⟨hp⟩

  -- K を ZMod p 上のベクトル空間とみなす
  letI : Algebra (ZMod p) K :=
    ZMod.algebra K p

  -- f を K の ZMod p 上の次元とする
  let f : ℕ := Module.finrank (ZMod p) K

  -- 定理1 (i)：K の位数は p ^ f
  have hK : Fintype.card K = p ^ f :=
    finiteField_card_eq_pow_finrank K p

  -- 位数が等しいので L の位数も p ^ f
  have hL : Fintype.card L = p ^ f := by
    calc
      Fintype.card L = Fintype.card K := hcard.symm
      _ = p ^ f := hK

  -- L の標数も p である
  letI : CharP L p :=
    charP_of_card_eq_prime_pow hL

  -- 先ほど証明した同型を利用
  exact finiteFieldsRingEquiv K p f L hK hL

end SerreNumberTheory
