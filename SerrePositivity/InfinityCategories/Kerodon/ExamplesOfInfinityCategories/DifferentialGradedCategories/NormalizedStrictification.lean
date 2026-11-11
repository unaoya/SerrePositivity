module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.HomotopyStrictification
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.MHomotopyHomology
public import Mathlib.AlgebraicTopology.DoldKan.Normalized

/-!
# A.5 の低次厳密化の正規化 Moore 複体への移送

概要：厳密化で得た低次数の一致を、正規化した鎖写像の厳密な一致へ送る。
方針：Moore 複体の単射な包含と、その自然な射影を使う。
規約：KST Construction A.5 の右辺の augmentation 補正。非被約 C(H) を保ち、
因子内のホモトピーを正規化する。AW/shuffle の比較自体は別に構成する。
使われ方：正規化した二つの差のテンソルの低次数消滅。

対応節は Kerodon 2.5（Tag 00ND）。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open CategoryTheory HomologicalComplex AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {X Y : SimplicialObject C}

/-- 概要：同じ次数で一致する射の正規化も、その次数で一致する。
方針：正規化 Moore 複体の包含の単射性と自然性を使う。
規約：KST A.5、次数ごとの厳密な等式。使われ方：差の消滅の正規化。 -/
lemma normalizedMap_component_eq (f g : X ⟶ Y) (n : ℕ)
    (h : f.app (Opposite.op ⦋n⦌) = g.app (Opposite.op ⦋n⦌)) :
    ((normalizedMooreComplex C).map f).f n = ((normalizedMooreComplex C).map g).f n := by
  apply (cancel_mono (NormalizedMooreComplex.objX Y n).arrow).mp
  have hf := congrArg (fun q ↦ q.f n) ((inclusionOfMooreComplex C).naturality f)
  have hg := congrArg (fun q ↦ q.f n) ((inclusionOfMooreComplex C).naturality g)
  simp only [comp_f, inclusionOfMooreComplex_app, inclusionOfMooreComplexMap_f,
    ] at hf hg
  rw [hf, hg]
  change (NormalizedMooreComplex.objX X n).arrow ≫ f.app (Opposite.op ⦋n⦌) =
    (NormalizedMooreComplex.objX X n).arrow ≫ g.app (Opposite.op ⦋n⦌)
  rw [h]

/-- 概要：正規化した写像は交代面写像複体の写像の包含と射影による挟み込み。
方針：包含の自然性と分裂を合成する。
規約：KST A.5、Mathlib の Moore 複体と PInfty の模型。
使われ方：全次数ホモトピーの正規化への移送。 -/
lemma normalizedMap_eq_retract (f : X ⟶ Y) :
    (normalizedMooreComplex C).map f =
      (inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex C).map f) ≫
        PInftyToNormalizedMooreComplex Y := by
  have hn := (inclusionOfMooreComplex C).naturality f
  change (normalizedMooreComplex C).map f ≫ inclusionOfMooreComplexMap Y =
    inclusionOfMooreComplexMap X ≫ (alternatingFaceMapComplex C).map f at hn
  have hid : inclusionOfMooreComplexMap Y ≫ PInftyToNormalizedMooreComplex Y = 𝟙 _ :=
    (splitMonoInclusionOfMooreComplexMap Y).id
  rw [← hn, Category.assoc, hid, Category.comp_id]

/-- 概要：単体的な全次数ホモトピーは正規化した鎖写像の鎖ホモトピーを与える。
方針：交代面写像複体の鎖ホモトピーを包含と PInfty 射影で挟む。
規約：KST A.5、被約複体への変更を行わない。
使われ方：厳密化前後の比較を正規化したテンソルへ移す。 -/
def normalizedChainHomotopy {f g : X ⟶ Y} (h : SimplicialObject.Homotopy f g) :
    Homotopy ((normalizedMooreComplex C).map f) ((normalizedMooreComplex C).map g) :=
  (Homotopy.ofEq (normalizedMap_eq_retract f)).trans
    (((h.toChainHomotopy.compLeft (inclusionOfMooreComplexMap X)).compRight
      (PInftyToNormalizedMooreComplex Y)).trans
        (Homotopy.ofEq (normalizedMap_eq_retract g).symm))

variable {S : SSet.{u}} {D : SimplicialObject (ModuleCat.{u} ℤ)}
variable {f g : linearizedSpace S ⟶ D} {m : ℕ}

/-- 概要：厳密化した射の正規化は次数 ≤m で終点の正規化に一致。
方針：低次数の成分一致を Moore 複体の包含で検出する。
規約：KST A.5、零次を含む。使われ方：正規化した差の消滅。 -/
lemma LinearizedMHomotopy.normalized_strictifiedMap_eq_low
    (H : LinearizedMHomotopy f g m) (n : ℕ) (hn : n ≤ m) :
    ((normalizedMooreComplex _).map H.strictifiedMap).f n =
      ((normalizedMooreComplex _).map g).f n :=
  normalizedMap_component_eq _ _ n (H.strictifiedMap_eq_low n hn)

/-- 概要：正規化した厳密化写像と終点の差は次数 ≤m で零。
方針：正規化した写像の成分の等式を引き算する。
規約：KST A.5 の右辺の augmentation 補正。
使われ方：二つの差の正規化テンソルの消滅次数の評価。 -/
lemma LinearizedMHomotopy.normalized_strictifiedDifference_eq_zero
    (H : LinearizedMHomotopy f g m) (n : ℕ) (hn : n ≤ m) :
    ((normalizedMooreComplex _).map H.strictifiedMap -
      (normalizedMooreComplex _).map g).f n = 0 := by
  rw [sub_f_apply, H.normalized_strictifiedMap_eq_low n hn, sub_self]

/-- 概要：入力射と低次厳密化した射の正規化は全鎖ホモトピック。
方針：区間の両端間の単体的ホモトピーを正規化し、実両端を同定する。
規約：KST A.5、因子内での全次数の比較。
使われ方：AW/shuffle の比較後に元の入力へ戻す。 -/
def LinearizedMHomotopy.normalizedStrictificationHomotopy
    (H : LinearizedMHomotopy f g m) :
    Homotopy ((normalizedMooreComplex _).map f)
      ((normalizedMooreComplex _).map H.strictifiedMap) :=
  (Homotopy.ofEq (congrArg ((normalizedMooreComplex _).map)
      H.strictificationHomotopy.h₀.symm)).trans
    ((normalizedChainHomotopy
      ((linearizedCylinderHomotopy S).postcomp H.strictificationHomotopy.h)).trans
      (Homotopy.ofEq (congrArg ((normalizedMooreComplex _).map)
        H.strictificationHomotopy.h₁)))

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
