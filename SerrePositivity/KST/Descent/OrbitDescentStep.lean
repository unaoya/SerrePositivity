module

public import SerrePositivity.KST.Descent.ExceptionalCopiesAction
public import SerrePositivity.KST.Descent.OrbitProductComparison
public import SerrePositivity.KST.Descent.ReducedSourceDescent

/-!
# 実際の軌道正方形の帰納段階

## 概要
軌道の二つの非交和の (3.8) と中心上の降下から、V → B の全次数の指定降下比較を証明する。

## 方針
例外部分の実際のコピー分解を使い、比較立方体の左上の固定比較の同型性を導く。
中項は既存の (3.8) と中心上の降下の積の比較で処理する。
自然な長完全列の五項補題を適用し、公開する PiDescent へ移す。

## 規約
長完全列とその自然性、前層の有限非交和の値の積保存は、実降下から供給すべき条件。
中心上の降下を次元帰納で証明することと、切断の被覆を幾何的推移性から得ることは残る。

## 使われ方
論文 定理 3.1 の「整 → 被約 → 一般」の帰納で用いる実際の軌道段階。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace SerrePositivity.KST.Descent.NaturalBlowupSequences

variable {S : Scheme.{u}} {B V : FiniteTypeSchemes S} {I : Type u} [Finite I]
variable {Coefficient : Type w}
variable {L : GradedPresheaf.{u + 1, u, w, t} (FiniteTypeSchemes S) Coefficient}

/-- 概要：(3.8) から実際の軌道比較の例外部分の固定比較は全単射（定理 3.1）。
方針：例外部分のコピーの作用と指定 fold の降下を、列の固定比較へ移す。
規約：例外部分の比較の同型性を仮定として入力しない。
使われ方：軌道正方形の五項補題の例外部分の辺。 -/
theorem orbitExceptionalComparison_bijective (data : NaturalBlowupSequences L)
    [IsReduced V.obj.left] {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op
      (reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom))))) (L H n)]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (H : Coefficient) (n : ℤ) :
    Function.Bijective ((data.orbitFixedComparison p sections section_identity covering
      action over_base equivariant H).mapC n) := by
  have descent := orbitExceptional_piDescent_of_preservesProduct p sections section_identity
    action over_base equivariant L
  exact L.fixedPullbackIntertwining_bijective H n
    (orbitExceptionalProjection p sections section_identity)
    (orbitExceptionalAction p sections section_identity action over_base equivariant)
    (orbitExceptionalProjection_invariant p sections section_identity action over_base equivariant)
    (descent H n)

/-- 概要：中心上の降下から実際の軌道正方形の全次数降下（論文 定理 3.1）。
方針：中項と例外部分を二つの実際のコピー分解の (3.8) で処理し、中心上の降下を貼る。
規約：中項・例外部分の同型性は追加仮定とせず、有限非交和の積保存から導出する。
使われ方：真閉中心への次元帰納の仮定を元の V → B の降下へ移す。 -/
theorem orbit_piDescent_of_center (data : NaturalBlowupSequences L)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)]
    [IsReduced V.obj.left] {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op
      (reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom))))) (L H n)]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (center_descent : L.PiDescent
      (closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
      (orbitCenterAction p sections action over_base)
      (orbitCenterProjection_invariant p sections action over_base)) :
    L.PiDescent p action over_base :=
  data.orbit_piDescent_of_center_and_exceptional p sections section_identity covering
    action over_base equivariant center_descent
    (data.orbitExceptionalComparison_bijective p sections section_identity covering
      action over_base equivariant)

/-- 概要：被約化した中心上の降下から実際の軌道降下（論文 補題 3.3・定理 3.1）。
方針：中心の始域だけを被約化した比較を公理 (3) で移し、軌道段階に入力する。
規約：中心の基底 Z は固定する。帰納仮定そのものの証明は別に必要。
使われ方：被約な有限型対象に対する次元帰納と、非被約な軌道中心の接続。 -/
theorem orbit_piDescent_of_reduced_center (data : NaturalBlowupSequences L)
    [IsNoetherian S] [Nilinvariant S L]
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op B)) (L H n)]
    [IsReduced V.obj.left] {G : Type*} [Group G] [Finite G] [MulAction G I]
    [MulAction.IsPretransitive G I] [Nonempty I]
    (p : V ⟶ B) [IsSeparated p.hom.left] [IsSeparated V.obj.hom]
    (sections : I → (B ⟶ V)) (section_identity : ∀ i, sections i ≫ p = 𝟙 B)
    (covering : ⋃ i, Set.range (sections i).hom.left = Set.univ)
    [∀ H n, PreservesLimit (Discrete.functor (fun _ : I ↦ op
      (reducedClosedAsFiniteType B (coincidenceClosedSet (fun i ↦ (sections i).hom))))) (L H n)]
    (action : G →* Aut V) (over_base : ∀ g, (action g).asIso.hom ≫ p = p)
    (equivariant : ∀ g i, sections (g • i) = sections i ≫ (action g).asIso.hom)
    (center_descent : L.PiDescent
      (finiteTypeReductionInclusion
          (closedCenterPullback p (coincidenceClosedSet (fun i ↦ (sections i).hom))) ≫
        closedCenterPullbackSecond p (coincidenceClosedSet (fun i ↦ (sections i).hom)))
      (finiteTypeReductionAction (orbitCenterAction p sections action over_base))
      (reducedSourceAction_over_base _ _
        (orbitCenterProjection_invariant p sections action over_base))) :
    L.PiDescent p action over_base := by
  apply data.orbit_piDescent_of_center p sections section_identity covering
    action over_base equivariant
  exact (Nilinvariant.piDescent_iff_reducedSource L _ _
    (orbitCenterProjection_invariant p sections action over_base)).mpr center_descent

end SerrePositivity.KST.Descent.NaturalBlowupSequences
