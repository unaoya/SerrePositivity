module

public import SerrePositivity.BhattScholze.Andre.Transfinite.Existence
open SerrePositivity SerrePositivity.BhattScholze.Andre.Transfinite
open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject
@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre.Transfinite
variable {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    {σ : Type u} (f : σ → Polynomial R)
/-- ## 概要
固定基底 R の多項式族の一項が、塔の代数 X 内に根を持つという性質を表す。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
元の多項式を X の標準係数射で評価する存在命題を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
def HasBasePolynomialRoot (X : AndreTowerAlgebra R p) (s : σ) : Prop :=
  ∃ x : X, (f s).eval₂ X.baseMap x = 0
/-- ## 概要
固定基底の多項式の根の存在は、塔の代数の任意の射に沿って保存される。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
根を環射で写し、係数射の両立性と評価の自然性を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem hasBasePolynomialRoot_map {X Y : AndreTowerAlgebra R p} (φ : X ⟶ Y) {s : σ}
    (h : HasBasePolynomialRoot f X s) : HasBasePolynomialRoot f Y s := by
  obtain ⟨x, hx⟩ := h
  refine ⟨φ.toRingHom x, ?_⟩
  rw [← φ.commutes, ← Polynomial.hom_eval₂, hx, map_zero]
variable (grow : ∀ (X : AndreTowerAlgebra R p) (s : σ),
    ∃ (Y : AndreTowerAlgebra R p) (_ : X ⟶ Y), HasBasePolynomialRoot f Y s)
include grow in
/-- ## 概要
各多項式一項の根を持つ拡大があれば、全族の根を既に持つか、未解決の一項の根を新たに持つ後続対象を得る。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
全族が解決済みなら恒等射を使う。そうでなければ未解決の添字を選び、その一項の拡大を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem exists_rootAdvancement (X : AndreTowerAlgebra R p) :
    ∃ (Y : AndreTowerAlgebra R p) (_ : X ⟶ Y),
      (∀ s, HasBasePolynomialRoot f X s) ∨
        ∃ s, ¬ HasBasePolynomialRoot f X s ∧ HasBasePolynomialRoot f Y s := by
  classical
  by_cases h : ∀ s, HasBasePolynomialRoot f X s
  · exact ⟨X, 𝟙 X, Or.inl h⟩
  obtain ⟨s, hs⟩ := not_forall.mp h
  obtain ⟨Y, φ, hy⟩ := grow X s
  exact ⟨Y, φ, Or.inr ⟨s, hs, hy⟩⟩
/-- ## 概要
未解決の一項を解決する後続対象を選ぶ。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
証明済みの一項前進の存在に Classical.choose を適用する。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
def rootAdvancement (X : AndreTowerAlgebra R p) : AndreTowerAlgebra R p :=
  (exists_rootAdvancement f grow X).choose
/-- ## 概要
選んだ一項前進の対象への、固定基底と両立する射を取り出す。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
同じ存在証明の射の選択を使う。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
def rootAdvancementMap (X : AndreTowerAlgebra R p) : X ⟶ rootAdvancement f grow X :=
  (exists_rootAdvancement f grow X).choose_spec.choose
/-- ## 概要
選んだ後続対象では、全族が既に解決済みか、前段で未解決の一項が解決される。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
前進対象と射の同じ選択に付随する条件を取り出す。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem rootAdvancement_spec (X : AndreTowerAlgebra R p) :
    (∀ s, HasBasePolynomialRoot f X s) ∨
      ∃ s, ¬ HasBasePolynomialRoot f X s ∧
        HasBasePolynomialRoot f (rootAdvancement f grow X) s :=
  (exists_rootAdvancement f grow X).choose_spec.choose_spec
include grow in
/-- ## 概要
固定基底の任意の多項式族について、各対象・各一項に根を持つ拡大が可能なら、
全族の根を持つ一つの perfectoid・p 完全忠実平坦な代数が存在する。
BS Thm 7.14（著者版 p.61）の一段根添加を任意族へ拡張する補助反復。

## 方針
添字族の濃度と可算濃度の上限の後続基数を取り、その始順序数に沿って未解決の一項を
解決する操作を反復する。終段で全族が解決しなければ、各段で新たに解決した添字は互いに異なる。
始順序数から元の添字族への単射が生じ、後続基数の定義に反する。

## 規約
多項式の係数は固定基底 R に属する。環・族の添字・反復の添字は Type u。
完備化後の係数を前段へ降ろす主張には使わない。

## 使われ方
A1 の一元根付き拡大から、正次数条件付きの指定 step を元の型で構成する。
-/
theorem exists_allBasePolynomialRoots (hR : IsIntegralPerfectoid R p) :
    ∃ X : AndreTowerAlgebra R p, ∀ s, HasBasePolynomialRoot f X s := by
  classical
  let c := Order.succ (Cardinal.mk σ ⊔ Cardinal.aleph0)
  let J := Ordinal.ToType c.ord
  have hc : Cardinal.aleph0 ≤ c := le_sup_right.trans (le_of_lt (Order.lt_succ _))
  have hlim := Cardinal.isSuccLimit_ord hc
  let : Nonempty J := Ordinal.nonempty_toType_iff.mpr hlim.ne_bot
  let : OrderBot J := WellFoundedLT.toOrderBot J
  let : NoMaxOrder J := by
    apply Ordinal.isSuccPrelimit_type_lt_iff.mp
    rw [Ordinal.type_toType]
    exact hlim.isSuccPrelimit
  let Φ : SuccStruct (AndreTowerAlgebra R p) :=
    { X₀ := ⟨R, RingHom.id R, hR, isCompletelyFaithfullyFlat_self R _⟩
      succ := rootAdvancement f grow
      toSucc := rootAdvancementMap f grow }
  let F := Φ.iterationFunctor J
  let Z := Φ.iteration J
  refine ⟨Z, ?_⟩
  by_contra hZ
  have hnot (i : J) : ¬ ∀ s, HasBasePolynomialRoot f (F.obj i) s := by
    intro hi
    exact hZ (fun s ↦ hasBasePolynomialRoot_map f ((Φ.iterationCocone J).ι.app i) (hi s))
  have hnew (i : J) : ∃ s, ¬ HasBasePolynomialRoot f (F.obj i) s ∧
      HasBasePolynomialRoot f (rootAdvancement f grow (F.obj i)) s :=
    (rootAdvancement_spec f grow (F.obj i)).resolve_left (hnot i)
  choose label hbefore hafter using hnew
  have hneq (i j : J) (hij : i < j) : label i ≠ label j := by
    intro heq
    apply hbefore j
    rw [← heq]
    let e := Φ.iterationFunctorObjSuccIso i (not_isMax i)
    have hi : HasBasePolynomialRoot f (F.obj (Order.succ i)) (label i) :=
      hasBasePolynomialRoot_map f e.inv (hafter i)
    exact hasBasePolynomialRoot_map f (F.map (homOfLE (Order.succ_le_of_lt hij))) hi
  have hinj : Function.Injective label := by
    intro i j heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact hneq i j h heq
    · exact hneq j i h heq.symm
  have hcard : Cardinal.mk J ≤ Cardinal.mk σ := Cardinal.mk_le_of_injective hinj
  have hJ : Cardinal.mk J = c := by
    dsimp only [J]
    rw [Cardinal.mk_toType, Cardinal.card_ord]
  rw [hJ] at hcard
  exact (not_le_of_gt (Order.lt_succ (Cardinal.mk σ ⊔ Cardinal.aleph0)))
    (hcard.trans le_sup_left)
end SerrePositivity.BhattScholze.Andre.Transfinite
