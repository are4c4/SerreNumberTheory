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
`x ^ (p ^ f) = x`を満たす元全体がなす集合は`Ω`の部分体になる．
-/
def frobeniusFixedSubfield : Subfield Ω where

  -- 部分体を構成する元の集合を定義
  carrier := {x : Ω | (iterateFrobenius Ω p f) x = x}
    -- interateFrobenius Ω p f : (x : Ω) ↦ (x ^ p ^ f : Ω)

  -- 0を含む
  zero_mem' := by
    change (iterateFrobenius Ω p f) 0 = 0
      -- 集合の定義を展開
    exact (iterateFrobenius Ω p f).map_zero
      -- RingHom.map_zero : 環準同型は0を0に送る

  -- 1を含む
  one_mem' := by
    change (iterateFrobenius Ω p f) 1 = 1
    exact (iterateFrobenius Ω p f).map_one
      -- RingHom.map_one : 環準同型は1を1に送る

  -- 加法について閉じている
  add_mem' := by
    intro x y hx hy
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) y = y at hy
    change (iterateFrobenius Ω p f) (x + y) = x + y
    rw [(iterateFrobenius Ω p f).map_add, hx, hy]
      -- RingHom.map_add : 環準同型は加法を保つ（f (a + b) = f a + f b）

  -- 乗法について閉じている
  mul_mem' := by
    intro x y hx hy
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) y = y at hy
    change (iterateFrobenius Ω p f) (x * y) = x * y
    rw [(iterateFrobenius Ω p f).map_mul, hx, hy]
      -- RingHom.map_mul : 環準同型は乗法を保つ（f (a * b) = f a * f b）

  -- 加法逆元について閉じている
  neg_mem' := by
    intro x hx
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) (-x) = -x
    rw [(iterateFrobenius Ω p f).map_neg, hx]
      -- RingHom.map_neg : f (-x) = -f x

  -- 乗法逆元について閉じている
  inv_mem' := by
    intro x hx
    change (iterateFrobenius Ω p f) x = x at hx
    change (iterateFrobenius Ω p f) x⁻¹ = x⁻¹
    rw [iterateFrobenius_def] at hx ⊢
      -- iterateFrobenius_def : (iterateFrobenius R p n) x = x ^ p ^ n
    rw [inv_pow, hx]
      -- inv_pow : a⁻¹ ^ n = (a ^ n)⁻¹

/--
`x`が`frobeniusFixedSubfield Ω p f`に属することと，
`x ^ (p ^ f) = x`であることは同値である．
-/
@[simp]
theorem mem_frobeniusFixedSubfield_iff
    (x : Ω) :
    x ∈ frobeniusFixedSubfield Ω p f ↔ x ^ (p ^ f) = x := by
  change (iterateFrobenius Ω p f) x = x ↔ x ^ (p ^ f) = x
  rw [iterateFrobenius_def]

/--
`x`が`frobeniusFixedSubfield Ω p f`に属することと，
`X ^ (p ^ f) - X`の根であることは同値である．
-/
theorem mem_frobeniusFixedSubfield_iff_isRoot
    (x : Ω) :
    x ∈ frobeniusFixedSubfield Ω p f ↔
      Polynomial.IsRoot (Polynomial.X ^ (p ^ f) - Polynomial.X) x := by
  rw [mem_frobeniusFixedSubfield_iff]
  change
    x ^ (p ^ f) = x ↔
    Polynomial.eval x (Polynomial.X ^ (p ^ f) - Polynomial.X) = 0
  rw [
      -- (X^{p^f} - X)(x)
    Polynomial.eval_sub,
      -- (X^{p^f})(x) - X(x)
    Polynomial.eval_pow,
      -- (X(x))^{p^f} - X(x)
    Polynomial.eval_X
      -- x^{p^f} - x
  ]
  -- x ^ p ^ f = x ↔ x ^ p ^ f - x = 0
  constructor
  · -- x ^ p ^ f = x → x ^ p ^ f - x = 0
    intro hx
    exact sub_eq_zero.mpr hx
  · -- x ^ p ^ f - x = 0 → x ^ p ^ f = x
    intro hx
    exact sub_eq_zero.mp hx

omit [Fact p.Prime] [CharP Ω p] in
/--
代数閉体`Ω`上で，
`X ^ (p ^ f) - X`は完全に分解する．
-/
theorem frobeniusPolynomial_splits
    [IsAlgClosed Ω] :
      -- Ω : 代数閉体
    (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).Splits := by
      -- : Polynomial Ω : Ω上の多項式であることを指定
      -- Polynomial.Splits : その多項式が完全に分解するという命題
  exact IsAlgClosed.splits (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω)
      -- IsAlgClosed.splits P : 代数閉体上の多項式Pは完全に分解する


omit [Fact p.Prime] in
/--
標数 `p` の体 `Ω` において，
`X ^ (p ^ f) - X` の形式的微分は `-1` である．
-/
theorem frobeniusPolynomial_derivative
    (hf : f ≠ 0) :
    (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).derivative = -1 := by
      -- Polynomial.derivative : その多項式の形式的微分

  -- 標数pではp^fが0になる
  have hcoeff : ((p ^ f : ℕ) : Ω) = 0 := by
    -- ((p ^ f : ℕ) : Ω) 自然数p^fを体Ωの元（pᶠ·1_Ω）として考える
    apply (CharP.cast_eq_zero_iff Ω p (p^f)).mpr
      -- CharP.cast_eq_zero_iff Ω p x : x = 0 ↔ p ∣ x
    exact dvd_pow_self p hf
      -- dvd_pow_self a (n ≠ 0) : a | aⁿ

  -- 微分の計算
  rw [
    -- (X^{p^f} - X)' = -1
    Polynomial.derivative_sub,
    -- (X^{p^f})' - X' = -1
    Polynomial.derivative_X_pow,
    -- {p^f}X^{p^f-1} - X' = -1
    Polynomial.derivative_X,
    -- {p^f}X^{p^f-1} - 1 = -1
  ]

  -- p ^ f = 0 を代入して整理する
  simp [hcoeff]

omit [Fact (Nat.Prime p)] in
/--
標数 `p` において，
`X ^ (p ^ f) - X` は分離多項式である．
-/
theorem frobeniusPolynomial_separable
    (hf : f ≠ 0) :
    (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).Separable := by
      -- Polynomial.Separable : その多項式が分離多項式
      --  ( Mathlibでは分離多項式を，もとの多項式とその形式的微分が互いに素である多項式と定義している )
  rw [
    Polynomial.separable_def,
      -- Polynomial.separable_def : Polynomial.Separable ↔ もとの多項式とその形式的微分が互いに素
    frobeniusPolynomial_derivative Ω p f hf
      -- 標数 `p` の体 `Ω` において，`X ^ (p ^ f) - X` の形式的微分は `-1`
  ]
  exact isCoprime_one_right.neg_right
    -- isCoprime_one_right : 任意のxと1は互いに素
    -- IsCoprime.neg_right : xとyが互いに素 → xと-yも互いに素

omit [CharP Ω p] in
/--
`f ≠ 0`ならば，
`X ^ (p ^ f) - X`の次数は`p ^ f`である．
-/
theorem frobeniusPolynomial_natDegree
    (hf : f ≠ 0) :
    (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).natDegree = p ^ f := by
      -- Polynomial.natDegree : その多項式の次数．ただし，零多項式の次数は0とする．

  -- 1 < p
  have hp_one_lt : 1 < p := by
    apply Nat.Prime.one_lt
      -- Nat.Prime.one_lt : 素数は1よりも大きい
    exact (Fact.out : Nat.Prime p)
      -- 型クラス Fact に格納されている命題の証明を取り出す

  -- 1 < p ^ f
  have hpow_one_lt : 1 < p ^ f := by
    exact Nat.one_lt_pow hf hp_one_lt
      -- Nat.one_lt_pow : n ≠ 0, 1 < a → 1 < a ^ n

  -- deg(X ^ (p ^ f) - X) = p ^ f
  calc
    -- deg(X ^ (p ^ f) - X) = deg(X ^ (p ^ f))
    (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).natDegree
      = (Polynomial.X ^ (p ^ f) : Polynomial Ω).natDegree := by
        apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
          -- q.natDegree < p.natDegree → (p - q).natDegree = p.natDegree
        simp only [
          Polynomial.natDegree_X,
            -- Polynomial.X.natDegree = 1
          Polynomial.natDegree_X_pow
            -- (Polynomial.X ^ n).natDegree = n
        ]
        exact hpow_one_lt

    -- deg(X ^ (p ^ f)) = p ^ f
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
      ((Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).rootSet Ω)
        -- Polynomial.rootSet : 多項式の根全体からなる集合
        -- ↑ : 根からなる集合を根からなる型に変換 -- なくてもよい
      = p ^ f := by
  calc
    -- Card((X ^ (p ^ f) - X)の根) = deg(X ^ (p ^ f) - X)
    Fintype.card
      ((Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).rootSet Ω)
      = (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).natDegree := by
        apply Polynomial.card_rootSet_eq_natDegree
          -- pが分離多項式，pが完全に分解する → Fintype.card ↑(p.rootSet K) = p.natDegree

        · -- pが分離多項式
          exact frobeniusPolynomial_separable Ω p f hf

        · -- pが完全に分解する
          -- 代数閉体Ω上で， X ^ (p ^ f) - Xは完全に分解する
          have hsplit :
              (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).Splits := by
            exact frobeniusPolynomial_splits Ω p f
          -- Ω上の多項式をΩ上の多項式に送っても変わらない
          have hmap :
              Polynomial.map (algebraMap Ω Ω)
                (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω)
                = (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω) := by
            simp
          rw [hmap]
          exact hsplit

    -- deg(X ^ (p ^ f) - X) = p ^ f
    _ = p ^ f := by
      exact frobeniusPolynomial_natDegree Ω p f hf

/--
`frobeniusFixedSubfield Ω p f`の台集合は，
`X ^ (p ^ f) - X`の根集合と一致する．
-/
theorem frobeniusFixedSubfield_carrier_eq_rootSet
    (hf : f ≠ 0) :
    (frobeniusFixedSubfield Ω p f).carrier
      = ((Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).rootSet Ω) := by
        -- : .carrier : 台集合を取り出す
  let P : Polynomial Ω := Polynomial.X ^ (p ^ f) - Polynomial.X

  -- Pは0ではない
  have hP_ne : P ≠ 0 := by
    change (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω) ≠ 0
    exact (frobeniusPolynomial_separable Ω p f hf).ne_zero
      -- Polynomial.Separable.ne_zero : 分離多項式は0ではない

  ext x
  change (x ∈ frobeniusFixedSubfield Ω p f) ↔ x ∈ P.rootSet Ω
  rw [Polynomial.mem_rootSet_of_ne hP_ne]
    -- a ∈ p.rootSet S ↔ p(a) = 0
  simpa [P, Polynomial.IsRoot] using (mem_frobeniusFixedSubfield_iff_isRoot Ω p f x)

/--
代数閉体`Ω`の部分体`frobeniusFixedSubfield Ω p f`は，
`p ^ f`個の元を持つ．
-/
theorem frobeniusFixedSubfield_natCard
    [IsAlgClosed Ω]
    (hf : f ≠ 0) :
    Nat.card (frobeniusFixedSubfield Ω p f) = p ^ f := by
  let P : Polynomial Ω := Polynomial.X ^ (p ^ f) - Polynomial.X

  -- frobeniusFixedSubfieldとPの根全体の集合の間に全単射を構成する
  let e : frobeniusFixedSubfield Ω p f ≃ ↑(P.rootSet Ω) := by
    exact Equiv.setCongr (frobeniusFixedSubfield_carrier_eq_rootSet Ω p f hf)
      -- Equiv.setCongr : 2つの集合が等しければ全単射が存在する

  -- |frobeniusFixedSubfield| = p ^ f
  calc
    Nat.card (frobeniusFixedSubfield Ω p f)
      = Nat.card ↑(P.rootSet Ω) := by
      exact Nat.card_congr e
        -- Nat.card_congr : 全単射が存在するなら，濃度が等しい

    _ = Fintype.card ↑(P.rootSet Ω) := by
      exact Nat.card_eq_fintype_card

    _ = p ^ f := by
      simpa [P] using
        frobeniusPolynomial_rootSet_card Ω p f hf

/--
`Ω`の有限部分体で`p ^ f`個の元を持つものは，
`frobeniusFixedSubfield Ω p f`に含まれる．
-/
theorem subfield_le_frobeniusFixedSubfield
    (L : Subfield Ω)
    [Fintype L]
    (hcard : Fintype.card L = p ^ f) :
    L ≤ frobeniusFixedSubfield Ω p f := by
      -- ≤ : 集合の包含関係を表す
      --  (Leanでは型によって≤の意味が変わる．ここでは部分体の包含関係を表している．)
  intro x hx
  rw[mem_frobeniusFixedSubfield_iff]
  let y : L := ⟨x, hx⟩
    -- L : Subfield Ωを部分型{x : Ω // x ∈ L}として扱う

  have hy : y ^ Fintype.card L = y := by
    by_cases hy0 : y = 0
    · -- 場合①：y = 0のとき
      rw[hy0]
      apply zero_pow
      exact Fintype.card_ne_zero
        -- Fintype.card α ≠ 0
    · -- 場合②：y ≠ 0のとき
      have hy_order : y ^ (Fintype.card L - 1) = 1 := by
        calc
          y ^ (Fintype.card L - 1)
              = (Units.mk0 y hy0 ^ (Fintype.card L - 1) : Lˣ).val := by
                -- Units.mk0 : 非零元から単元を構成する（有限体Lの非零元を乗法群Lˣの元として扱う）
                -- Lˣ : 体Lの乗法群を表す型
                -- .val : Lˣの項から値（型はL）を取り出す
                rw [Units.val_pow_eq_pow_val]
                  -- Units.val_pow_eq_pow_val : ((u : Lˣ) ^ n).val = (u.val : L) ^ n
                  --   単元を累乗してから値を取り出しても、先に値を取り出してから累乗しても結果は同じ
                rw [Units.val_mk0]
                  -- Units.val_mk0 : (Units.mk0 y hy0 : Lˣ).val = (y : L)
                  --   元の体の非零元を単元に変換してから .val で取り出すと，元の値に戻る
            _ = 1 := by
                classical
                  -- Fintype.card_unitsを使うために必要
                  --   [DecidableEq α]で排中律を使っている
                rw [← Fintype.card_units]
                  -- Fintype.card αˣ = Fintype.card α - 1
                rw [pow_card_eq_one]
                  -- (x : G) ^ Fintype.card G = 1 （ラグランジュの定理）
                rfl
      rw [
        ← Nat.succ_pred_eq_of_pos Fintype.card_pos,
          -- Nat.succ_pred_eq_of_pos : 0 < n → n.pred.succ = n
          --   n.predはn-1，n.succはn+1だから，n.pred.succはn-1+1
          -- Fintype.card_pos : 0 < Fintype.card α
        pow_succ,
          -- pow_succ : a ^ (n + 1) = a ^ n * a
        Nat.pred_eq_sub_one,
          -- Nat.pred_eq_sub_one : n.pred = n - 1
        hy_order,
        one_mul
      ]

  have hyΩ : (y : Ω) ^ Fintype.card L = (y : Ω) := by
    exact congrArg (fun z : L => (z : Ω)) hy
      -- congrArg : a = b → f(a) = f(b)
      -- (fun z : L => (z : Ω))はLからΩへの包含写像
  change (y : Ω) ^ (p ^ f) = (y : Ω)
  rw [← hcard]
  exact hyΩ

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
    -- SetLike.coe_injective : 部分体の台集合同士が等しければ部分体同士も等しい
    --   Function.Injective : ∀ x y, f x = f y → x = y
    --   SetLike.coe : 台集合を取り出す関数
    --   OutParam : 型クラスの探索において、どの型引数をインスタンスから決定するかを指定する仕組み
  apply Set.Finite.eq_of_subset_of_card_le
    -- Set.Finite.eq_of_subset_of_card_le : 有限集合S,Tについて，S⊆T,|T|≤|S| → S=T

  · -- (frobeniusFixedSubfield Ω p f)は有限集合
    change (frobeniusFixedSubfield Ω p f).carrier.Finite
    rw [frobeniusFixedSubfield_carrier_eq_rootSet Ω p f hf]
      -- frobeniusFixedSubfield Ω p fの台集合は， X ^ (p ^ f) - Xの根集合と一致する
    exact (Polynomial.X ^ (p ^ f) - Polynomial.X : Polynomial Ω).rootSet_finite Ω
      -- Polynomial.rootSet_finite : 体上の非零多項式の根集合は有限

  · -- L ⊆ (frobeniusFixedSubfield Ω p f)
    exact subfield_le_frobeniusFixedSubfield Ω p f L hcard

  · -- |(frobeniusFixedSubfield Ω p f)| ≤ L
      -- 両辺は，部分体 → ↑部分体の台集合 → ↑↑部分体の台集合の元からなる部分型，と型強制される
    change Nat.card (frobeniusFixedSubfield Ω p f) ≤ Nat.card L
    rw [
      frobeniusFixedSubfield_natCard Ω p f hf,
        -- 代数閉体Ωの部分体(frobeniusFixedSubfield Ω p f)は， p ^ f個の元を持つ
      Nat.card_eq_fintype_card,
        -- Nat.card_eq_fintype_card : Nat.card α = Fintype.card α
        --   Finite α : αは有限である
        --   Fintyoe α : αの全要素を列挙できる
      hcard
    ]

/--
代数閉体`Ω`の中には，`p ^ f`個の元を持つ部分体が一意に存在する．
その部分体は`frobeniusFixedSubfield Ω p f`である．
-/
theorem existsUnique_subfield_natCard_eq_pow
    [IsAlgClosed Ω]
    (hf : f ≠ 0) :
    ∃! L : Subfield Ω, Nat.card L = p ^ f := by
      -- ∃! : ExsitsUnipueという命題を表す記法

    -- 存在すること
    refine ⟨
      frobeniusFixedSubfield Ω p f,
        -- 存在する部分体の具体例
      frobeniusFixedSubfield_natCard Ω p f hf,
        -- その部分体の位数はp^fである
      ?_
        -- （残りのgoal）他に条件を満たす部分体があればそれは具体例であげた部分体と等しい
    ⟩

    -- 一意性
    intro L hL
    have hpow_pos : 0 < p ^ f := by
      exact pow_pos (Fact.out : Nat.Prime p).pos f
        -- pow_pos : 0 < a → 0 < a ^ n
        -- Nat.Prime.pos : pが素数 → 0 < p

    have hL_ne : Nat.card L ≠ 0 := by
      rw [hL]
      exact ne_of_gt hpow_pos
        -- ne_of_gt : b < a → a ≠ b
        -- Nat.cardは無限型に対して0を返す

    letI : Finite L := by
      exact Nat.finite_of_card_ne_zero hL_ne
        -- Nat.finite_of_card_ne_zero : Nat.card α ≠ 0 → Finite α

    letI : Fintype L := by
      exact Fintype.ofFinite L

    have hcard : Fintype.card L = p ^ f := by
      rw [← Nat.card_eq_fintype_card]
      exact hL

    exact subfield_eq_frobeniusFixedSubfield Ω p f L hf hcard

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
標数 `p` の有限体 `K` を，`ZMod p` の代数閉包に埋め込む．
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
    -- AlgHom.toRingHom : 代数準同型は環準同型
    -- RingHom.fieldRange : 環準同型の像を部分体として取り出す

/--
`K` を代数閉包に埋め込んだ像の位数は，元の有限体 `K` の位数 `p ^ f` に等しい．
-/
theorem finiteFieldImageInClosure_natCard
    (hcard : Fintype.card K = p ^ f) :
    Nat.card (finiteFieldImageInClosure K p) = p ^ f := by

  -- φ : K から ((ZMod p)の代数閉包) への環準同型
  let φ : K →+* AlgebraicClosure (ZMod p) :=
    (finiteFieldEmbeddingIntoClosure K p).toRingHom

  calc
    Nat.card (finiteFieldImageInClosure K p)
        = Nat.card φ.fieldRange := by
            rfl

    _ = Nat.card K := by
          exact Nat.card_congr (φ.rangeRestrictFieldEquiv.symm.toEquiv)
            -- RingHom.rangeRestrictFieldEquiv : 体から環準同型の像への体同型を構成
            -- RingEquiv.symm : 環同型の逆写像を環同型として構成
            -- RingEquiv.toEquiv : 環同型は全単射
            -- Nat.card_congr : 全単射があれば濃度が等しい

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
      frobeniusFixedSubfield (AlgebraicClosure (ZMod p)) p f := by

  obtain ⟨L, _, hUnique⟩ :=
    existsUnique_subfield_natCard_eq_pow (AlgebraicClosure (ZMod p)) p f hf
      -- L : 存在する部分体
      -- hUnique : 一意性の証明

  -- 埋め込んだ像の位数は p ^ f
  have hImage : Nat.card (finiteFieldImageInClosure K p) = p ^ f := by
    exact finiteFieldImageInClosure_natCard K p f hcard

  -- Frobenius固定部分体の位数も p ^ f
  have hFixed :
      Nat.card (frobeniusFixedSubfield (AlgebraicClosure (ZMod p)) p f) = p ^ f := by
    exact frobeniusFixedSubfield_natCard (AlgebraicClosure (ZMod p)) p f hf

  -- 一意性から両者は等しい
  calc
    finiteFieldImageInClosure K p
      = L := by
        exact hUnique (finiteFieldImageInClosure K p) hImage

    _ = frobeniusFixedSubfield (AlgebraicClosure (ZMod p)) p f := by
        exact (hUnique (frobeniusFixedSubfield (AlgebraicClosure (ZMod p)) p f) hFixed).symm

/--
位数が `p ^ f` の有限体 `K` は，
代数閉包内の `frobeniusFixedSubfield` と体同型（環同型）である．
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
      φ.fieldRange = frobeniusFixedSubfield (AlgebraicClosure (ZMod p)) p f := by
    exact finiteFieldImage_eq_frobeniusFixedSubfield K p f hf hcard

  -- K ≃ φ(K) と φ(K) = F_q を組み合わせる
  exact φ.rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr hImage)
    -- RingHom.rangeRestrictFieldEquiv : 環準同型の終域を像に制限すると環同型ができる
    -- RingEquiv.subfieldCongr : S = T ならば，SとTは同型

omit [Fact (Nat.Prime p)] [CharP K p] in
/--
位数が `p ^ f` である有限体では，指数 `f` は `0` ではない．
-/
theorem finiteField_pow_exponent_ne_zero
    (hcard : Fintype.card K = p ^ f) : f ≠ 0 := by

  intro hf

  -- f = 0 ならば，K の位数は高々 1
  have hcard_le_one : Fintype.card K ≤ 1 := by
    rw [hf, pow_zero] at hcard
    exact hcard.le

  -- しかし，体には 0 と 1 という異なる元が存在する
  have hsub : Subsingleton K :=
      -- Subsingleton : 任意の2つの元が等しい
    Fintype.card_le_one_iff_subsingleton.mp hcard_le_one
      -- Fintype.card_le_one_iff_subsingleton : 位数が1以下 ↔ 任意の2元が等しい

  exact not_subsingleton K hsub
    -- not_subsingleton : 元が少なくとも2つある型はSubsingletonではない

/--
標数 `p` で，ともに `p ^ f` 個の元を持つ2つの有限体 `K`, `L` は環同型である．
-/
noncomputable def finiteFieldsRingEquiv
    (L : Type*) [Field L] [Fintype L] [CharP L p]
    (hK : Fintype.card K = p ^ f)
    (hL : Fintype.card L = p ^ f) :
    K ≃+* L := by

  -- L に ZMod p 上の代数構造を入れる
  letI : Algebra (ZMod p) L := ZMod.algebra L p

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
