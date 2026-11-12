module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.ResolutionPaths

/-!
概要：coherent nerve の右 pinched 単体を旗の解像で評価する。
方針：固定面と固定終点で対象を正規化し、path の旗に豊穣関手の Hom の作用を適用する。
規約：まず単体ごとの評価を構成する。単体的な自然性は別途証明する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、豊穣 Hom と pinched 写像空間の比較。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory SimplicialThickening SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右 pinched な coherent 単体の先頭面の全対象は始域の対象。
方針：固定面の等式を豊穣関手の対象上で評価する。
規約：最後の頂点以外を castSucc で指定する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、豊穣 Hom の始域の正規化。 -/
lemma coherentPinched_sourceObj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (i : Fin (n + 1)) :
    τ.val.obj (⟨ULift.up i.castSucc⟩ : SimplicialThickening (ULift.{u} (Fin (n + 2)))) = X := by
  exact congrArg (fun F ↦ F.obj
    (⟨ULift.up i⟩ : SimplicialThickening (ULift.{u} (Fin (n + 1))))) τ.source

/-- 概要：右 pinched な coherent 単体の最後の対象は終域の対象。
方針：固定終点の等式を coherent nerve の零単体の対象で評価する。
規約：最後の頂点は追加した頂点。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、豊穣 Hom の終域の正規化。 -/
lemma coherentPinched_targetObj {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n) :
    τ.val.obj (⟨ULift.up (Fin.last (n + 1))⟩ :
      SimplicialThickening (ULift.{u} (Fin (n + 2)))) = Y := by
  exact congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (C := C)) τ.target

/-- 概要：右 pinched 単体の始域と終域を正規化した豊穣 Hom の作用。
方針：豊穣関手の作用の後に対象の等号による移送を行う。
規約：始点は先頭面の任意の頂点、終点は追加した最後の頂点。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、旗の評価を始域と終域の共通の Hom に入れる。 -/
noncomputable def coherentPinchedHom {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (i : Fin (n + 1)) :
    nerve (Path (ULift.up i.castSucc : ULift.{u} (Fin (n + 2)))
      (ULift.up (Fin.last (n + 1)))) ⟶ SimplicialCategory.sHom X Y :=
  τ.val.map ⟨ULift.up i.castSucc⟩ ⟨ULift.up (Fin.last (n + 1))⟩ ≫
    eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentPinched_sourceObj τ i) (coherentPinched_targetObj τ))

/-- 概要：右 pinched 単体を有限集合の旗で評価して豊穣 Hom の単体を得る。
方針：旗から作った path の単体に正規化した豊穣 Hom の作用を適用する。
規約：n は pinched 単体の次数、d は評価する旗の次数。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像から豊穣 Hom への写像の単体上の公式。 -/
noncomputable def coherentPinchedEvaluate {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n)
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) : (SimplicialCategory.sHom X Y) _⦋d⦌ :=
  (coherentPinchedHom τ F.start).app _ F.pathFlag

/-- 概要：豊穣 Hom から比較した pinched 単体の作用は最大元による評価。
方針：既存の比較単体の Hom の計算を端点の正規化と照合する。
規約：対象の等号の証明は証明の一意性により一致する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、比較写像と補助解像の射影の対応。 -/
lemma coherentPinchedHom_comparison {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ} (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (i : Fin (n + 1)) :
    coherentPinchedHom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonPinchedSimplex σ) i =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ := by
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonHom_cast_last σ i

/-- 概要：比較した pinched 単体の旗での評価は最大元の頂点列による引き戻し。
方針：正規化した Hom の作用を計算し、path の旗の最大元を比較する。
規約：旗の解像の射影を通じた評価という等式で述べる。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、比較射を射影の前合成として同定する計算。 -/
lemma coherentPinchedEvaluate_comparison {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n d : ℕ}
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌) (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.CoherentResolutionFlag n d) :
    coherentPinchedEvaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentHomComparisonPinchedSimplex σ) F =
      (SimplicialCategory.sHom X Y).map
        (SimplexCategory.mkHom ⟨F.maxAt, F.maxAt_monotone⟩).op σ := by
  unfold coherentPinchedEvaluate
  rw [coherentPinchedHom_comparison]
  have h : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap F.start).app (Opposite.op ⦋d⦌) F.pathFlag =
      ULift.up (SimplexCategory.mkHom ⟨F.maxAt, F.maxAt_monotone⟩) := by
    apply stdSimplex.ext
    intro i
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximum (F.toPath i) = F.maxAt i
    exact F.pathLastMaximum_toPath i
  change (SSet.yonedaEquiv.symm σ).app (Opposite.op ⦋d⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathLastMaximumMap F.start).app (Opposite.op ⦋d⦌) F.pathFlag) = _
  rw [h]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
