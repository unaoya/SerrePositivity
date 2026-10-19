module

public import SerrePositivity.KST.Comparison.LocalCoefficientAnodyne

/-!
# 基底上の相対局所係数ホモロジー

概要：基底上の包含の相対局所係数複体と長完全列を構成する。
方針：実際の正規化局所係数鎖写像の余核と蛇補題を使う。
規約：Weibel K-book IV.1.5–IV.1.6 の二・三セル添付の相対複体。
使われ方：plus のセル添付における局所係数の消滅の計算。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits
variable {B : SSet.{u}} (L : LocalCoefficientSystem B)

/--
概要：基底上の射の相対局所係数鎖複体。
方針：構成済みの正規化鎖写像の余核を取る。
規約：包含の場合に商複体を表す。
使われ方：セル添付の相対複体。
-/
def relativeOverLocalCoefficientChains {X Y : Over B} (i : X ⟶ Y) :
    ChainComplex AddCommGrpCat.{u} ℕ :=
  cokernel ((overLocalCoefficientChainsFunctor L).map i)

/--
概要：基底上の射の圏から相対局所係数複体への関手。
方針：可換正方形の余核写像とその関手法則を使う。
規約：固定した基底から係数を引き戻す。
使われ方：相対ホモロジーの自然性。
-/
def relativeOverLocalCoefficientChainsFunctor :
    Arrow (Over B) ⥤ ChainComplex AddCommGrpCat.{u} ℕ where
  obj i := relativeOverLocalCoefficientChains L i.hom
  map f := cokernel.map _ _ ((overLocalCoefficientChainsFunctor L).map f.left)
    ((overLocalCoefficientChainsFunctor L).map f.right) (by
      rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, f.w])
  map_id i := by
    apply (cancel_epi (cokernel.π ((overLocalCoefficientChainsFunctor L).map i.hom))).mp
    simp [relativeOverLocalCoefficientChains]
  map_comp {i j k} f g := by
    apply (cancel_epi (cokernel.π ((overLocalCoefficientChainsFunctor L).map i.hom))).mp
    simp [relativeOverLocalCoefficientChains, Category.assoc,
      CategoryTheory.Functor.map_comp]

/--
概要：基底上の射の相対局所係数ホモロジー。
方針：余核複体の実際のホモロジーを取る。
規約：非負整数次数。
使われ方：相対セルのホモロジー群。
-/
abbrev relativeOverLocalCoefficientHomology {X Y : Over B} (i : X ⟶ Y) (n : ℕ) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (ComplexShape.down ℕ) n).obj
    (relativeOverLocalCoefficientChains L i)

/--
概要：基底上の包含の局所係数鎖複体と相対複体の列。
方針：鎖写像の余核列を取る。
規約：包含以外でも右完全な三項複体を定める。
使われ方：包含の場合の短完全性。
-/
def relativeOverLocalCoefficientSequence {X Y : Over B} (i : X ⟶ Y) :
    ShortComplex (ChainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.cokernelSequence ((overLocalCoefficientChainsFunctor L).map i)

/--
概要：基底上の単射に対する相対局所係数複体の列は短完全である。
方針：証明済みの局所係数複体の単射保存を使う。
規約：係数群の平坦性は不要。
使われ方：相対ホモロジーの長完全列。
-/
theorem relativeOverLocalCoefficientSequence_shortExact {X Y : Over B}
    (i : X ⟶ Y) [Mono i] : (relativeOverLocalCoefficientSequence L i).ShortExact := by
  change (ShortComplex.cokernelSequence ((overLocalCoefficientChainsFunctor L).map i)).ShortExact
  exact {
    exact := ShortComplex.cokernelSequence_exact _
    mono_f := (overLocalCoefficientChainsFunctor L).map_mono i }

/--
概要：相対局所係数ホモロジーの連結射。
方針：実際の短完全列の蛇補題を適用する。
規約：H_(n+1)(Y,X) から H_n(X) へ向かう。
使われ方：二・三セル添付の相対ホモロジー。
-/
def relativeOverLocalCoefficientBoundary {X Y : Over B} (i : X ⟶ Y) [Mono i] (n : ℕ) :
    relativeOverLocalCoefficientHomology L i (n + 1) ⟶
      (overLocalHomologyFunctor L n).obj X :=
  (relativeOverLocalCoefficientSequence_shortExact L i).δ (n + 1) n rfl

/--
概要：局所係数の包含のホモロジー射から相対群への列は完全である。
方針：短完全列のホモロジー長完全列の第二の完全性。
規約：全ての非負整数次数。
使われ方：相対群の消滅から通常の群への比較。
-/
theorem relativeOverLocalCoefficient_exact_at_target {X Y : Over B}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    ((relativeOverLocalCoefficientSequence L i).map
      (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n)).Exact :=
  (relativeOverLocalCoefficientSequence_shortExact L i).homology_exact₂ n

/--
概要：相対局所係数ホモロジーの連結射と包含の誘導射の合成は零である。
方針：短完全列のホモロジー列の零合成を使う。
規約：非負整数次数。
使われ方：長完全列の始域側の完全性。
-/
@[reassoc] theorem relativeOverLocalCoefficient_boundary_comp {X Y : Over B}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    relativeOverLocalCoefficientBoundary L i n ≫ (overLocalHomologyFunctor L n).map i = 0 :=
  (relativeOverLocalCoefficientSequence_shortExact L i).δ_comp (n + 1) n rfl

/--
概要：相対局所係数ホモロジー列は始域のホモロジーで完全である。
方針：短完全列のホモロジー列の第一の完全性。
規約：相対群から包含の始域への連結射。
使われ方：セル添付の低次数の計算。
-/
theorem relativeOverLocalCoefficient_exact_at_source {X Y : Over B}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk (relativeOverLocalCoefficientBoundary L i n)
      ((overLocalHomologyFunctor L n).map i)
      (relativeOverLocalCoefficient_boundary_comp L i n)).Exact :=
  (relativeOverLocalCoefficientSequence_shortExact L i).homology_exact₁ (n + 1) n rfl

/--
概要：相対群への誘導射と連結射の合成は零である。
方針：短完全列のホモロジー列の零合成を使う。
規約：次数を一つ下げる連結射。
使われ方：相対群での完全性。
-/
@[reassoc] theorem relativeOverLocalCoefficient_comp_boundary {X Y : Over B}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    HomologicalComplex.homologyMap
      (cokernel.π ((overLocalCoefficientChainsFunctor L).map i)) (n + 1) ≫
      relativeOverLocalCoefficientBoundary L i n = 0 :=
  (relativeOverLocalCoefficientSequence_shortExact L i).comp_δ (n + 1) n rfl

/--
概要：相対局所係数ホモロジー列は相対群で完全である。
方針：短完全列のホモロジー列の第三の完全性。
規約：相対群への射から連結射へ続く部分。
使われ方：二・三セルの相対群の計算。
-/
theorem relativeOverLocalCoefficient_exact_at_relative {X Y : Over B}
    (i : X ⟶ Y) [Mono i] (n : ℕ) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap
        (cokernel.π ((overLocalCoefficientChainsFunctor L).map i)) (n + 1))
      (relativeOverLocalCoefficientBoundary L i n)
      (relativeOverLocalCoefficient_comp_boundary L i n)).Exact :=
  (relativeOverLocalCoefficientSequence_shortExact L i).homology_exact₃ (n + 1) n rfl

/--
概要：基底上の単射の局所係数ホモロジー同型性は相対複体の非輪状性と同値である。
方針：証明済みの単射鎖写像の余核による擬同型判定を使う。
規約：全次数のホモロジー消滅。
使われ方：plus の相対二・三セルの相殺の判定。
-/
theorem overLocalHomologyEquivalence_iff_relative_acyclic {X Y : Over B}
    (i : X ⟶ Y) [Mono i] :
    overLocalHomologyEquivalences L i ↔ (relativeOverLocalCoefficientChains L i).Acyclic := by
  rw [overLocalHomologyEquivalences_iff]
  exact integralChain_quasiIso_iff_cokernel_acyclic _

/--
概要：基底上の pushout の相対局所係数複体は自然に同型である。
方針：実際の余極限保存と pushout の余核同型を合成する。
規約：局所係数は共通の基底から引き戻す。
使われ方：セル添付の相対複体を標準セルで計算する。
-/
def relativeOverLocalCoefficientPushoutIso
    {X Y X' Y' : Over B} {t : X ⟶ Y} {l : X ⟶ X'} {r : Y ⟶ Y'} {b : X' ⟶ Y'}
    (sq : IsPushout t l r b) :
    relativeOverLocalCoefficientChains L t ≅ relativeOverLocalCoefficientChains L b := by
  let F := overLocalCoefficientChainsFunctor L
  have : IsIso (cokernel.map (F.map t) (F.map b) (F.map l) (F.map r)
      (by rw [← F.map_comp, ← F.map_comp, sq.w])) :=
    isIso_cokernel_map_of_isPushout (sq.map F)
  exact asIso (cokernel.map (F.map t) (F.map b) (F.map l) (F.map r)
    (by rw [← F.map_comp, ← F.map_comp, sq.w]))

end SerrePositivity.KST.Comparison
