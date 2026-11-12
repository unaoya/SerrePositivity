module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiscreteEmbedding
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.ChainMapEdge
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberConnectingShift
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-! # 加群の離散埋め込みの充満忠実性

概要：加群の関手的 semifree 解像度は h D(S) への充満忠実な埋め込みを与える。
方針：導来比較の後で次数零の単一複体と自然に同型であることを使う。
規約：加群の射を比較し、H⁰ の同型には D5b の増大射を使う。
使われ方：D6 の heart の射と離散対象の特徴づけ。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
open scoped _root_.Simplicial
variable (S : Type u) [CommRing S]

/-- 概要：加群の離散像を関手的 semifree 解像度の頂点として取る。
方針：D5b の閉零圏の対象から定値頂点を作る。
規約：選んだ自由解像度を共有する。使われ方：加群の埋め込みの対象。 -/
def moduleHeartVertex (M : ModuleCat.{u} S) : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (ForgetEnrichment.to (Complex S) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor S).obj M))

/-- 概要：加群を h D(S) へ送る離散埋め込み J。
方針：解像度の閉零射の H⁰ の類を N3 の充満忠実比較で引き戻す。
規約：対象は moduleHeartVertex。使われ方：heart の Hom 比較。 -/
def moduleHeartFunctor : ModuleCat.{u} S ⥤ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S where
  obj M := ⟨moduleHeartVertex S M⟩
  map f := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.preimage
    ((toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor S).map f))
  map_id M := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map_injective
    rw [Functor.map_preimage]
    exact (congrArg (toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor S).map_id M)).trans
        (((toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map_id _).trans
          ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map_id
            (⟨moduleHeartVertex S M⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S)).symm)
  map_comp f g := by
    apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map_injective
    simp only [Functor.map_preimage, Functor.map_comp]

variable [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：J の導来比較像は自由余鎖解像度の局所化に自然に同型である。
方針：ホモトピー商と導来局所化の標準比較の自然性を評価する。
規約：D3 の同値をそのまま使う。使われ方：次数零の単一複体との比較。 -/
def moduleHeartLocalizationIso :
    moduleHeartFunctor S ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor ≅
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S ⋙ DerivedCategory.Q :=
  NatIso.ofComponents (fun M => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedVertexLocalizationIso (moduleHeartVertex S M)) (by
    intro M N f
    change DerivedCategory.Qh.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeHomotopyComparison S).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map ((moduleHeartFunctor S).map f))) ≫ _ = _
    dsimp only [moduleHeartFunctor]
    rw [Functor.map_preimage]
    have h := (DerivedCategory.quotientCompQhIso (ModuleCat S)).hom.naturality
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f)
    change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex S).map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor S).map f))) ≫ _ = _
    dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor]
    rw [Functor.map_preimage]
    exact h)

/-- 概要：J の導来比較像は加群の次数零の単一複体に自然に同型である。
方針：D5b の増大擬同型を局所化で同型にする。
規約：すべての加群に自然。使われ方：充満忠実性の転送。 -/
def moduleHeartDerivedIso :
    moduleHeartFunctor S ⋙ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor ≅
      DerivedCategory.singleFunctor (ModuleCat S) 0 :=
  moduleHeartLocalizationIso S ≪≫ NatIso.ofComponents (fun M => by
    haveI := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation_quasiIso S M
    exact asIso (DerivedCategory.Q.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation S M))) (by
      intro M N f
      exact (DerivedCategory.Q.map_comp _ _).symm.trans
        ((congrArg DerivedCategory.Q.map ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentationNat S).naturality f)).trans
          (DerivedCategory.Q.map_comp _ _)))

/-- 概要：加群の離散埋め込み J は充満である。
方針：導来比較後の単一複体の充満性を忠実な同値で反映する。
規約：任意の可換環。使われ方：heart の射の存在。 -/
instance moduleHeartFunctor_full : (moduleHeartFunctor S).Full :=
  Functor.Full.of_comp_faithful_iso (moduleHeartDerivedIso S)

/-- 概要：加群の離散埋め込み J は忠実である。
方針：導来比較後の単一複体の忠実性を使う。
規約：加群の射の等式を反映する。使われ方：heart の射の一意性。 -/
instance moduleHeartFunctor_faithful : (moduleHeartFunctor S).Faithful :=
  Functor.Faithful.of_comp_iso (moduleHeartDerivedIso S)

/-- 概要：加群の射と離散像の h D(S) の射は全単射である。
方針：J の充満忠実性から Hom の同値を取る。
規約：順方向は J.map。使われ方：heart の充満忠実性の公開形。 -/
def moduleHeartHomEquiv (M N : ModuleCat.{u} S) :
    (M ⟶ N) ≃ ((moduleHeartFunctor S).obj M ⟶ (moduleHeartFunctor S).obj N) :=
  (Functor.FullyFaithful.ofFullyFaithful (moduleHeartFunctor S)).homEquiv

omit [HasDerivedCategory (ModuleCat S)] in
/-- 概要：D5b の自由解像度の零次同型は加群の射に自然である。
方針：増大射の自然性にホモロジーを適用し、単一複体の比較を合成する。
規約：既存の同じ増大同型。使われ方：JHZeroIso の自然性。 -/
lemma moduleFreeCochainHomologyZeroIso_naturality {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    HomologicalComplex.homologyMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f) 0 ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainHomologyZeroIso S N).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainHomologyZeroIso S M).hom ≫ f := by
  have h := congrArg (HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) 0).map
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentationNat S).naturality f)
  simp only [Functor.map_comp] at h
  change HomologicalComplex.homologyMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f) 0 ≫
    (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation S N) 0 ≫ _) =
      (HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation S M) 0 ≫ _) ≫ f
  change HomologicalComplex.homologyMap ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f) 0 ≫
    HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation S N) 0 =
      HomologicalComplex.homologyMap (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainAugmentation S M) 0 ≫
        HomologicalComplex.homologyMap ((HomologicalComplex.single _ _ 0).map f) 0 at h
  rw [← Category.assoc, h, Category.assoc, Category.assoc]
  exact congrArg (_ ≫ ·)
    (HomologicalComplex.singleObjHomologySelfIso_hom_naturality (.up ℤ) 0 f)

/-- 概要：J の H⁰ は元の加群に D5b の増大射を通じて同型である。
方針：D5d の頂点比較と D5b の零次ホモロジー同型を合成する。
規約：既存の JHZeroIso に相当する加群版。使われ方：heart の H⁰ の同定。 -/
def moduleHeartHZeroIso (M : ModuleCat.{u} S) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZero S (moduleHeartVertex S M) ≅ M :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroIso S (moduleHeartVertex S M) ≪≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainHomologyZeroIso S M

omit [HasDerivedCategory (ModuleCat S)] in
/-- 概要：J の射は関手的解像度の鎖写像の辺の類である。
方針：N3 の忠実比較の下で閉零射の像を比較する。
規約：同じ自由解像度の射。使われ方：H⁰ の自然性を辺の計算に帰着する。 -/
lemma moduleHeartFunctor_map_edge {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    (moduleHeartFunctor S).map f = SSet.Truncated.HomotopyCategory₂.homMk
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge (x := moduleHeartVertex S M) (y := moduleHeartVertex S N)
        ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map_injective
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityH0Equivalence S).functor.map
    ((moduleHeartFunctor S).map f) = (toHomotopy S (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)).map _
  dsimp only [moduleHeartFunctor]
  rw [Functor.map_preimage]
  congr 1
  apply (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.semifreeClosedToComplex S).map_injective
  dsimp only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleSemifreeResolutionFunctor]
  rw [Functor.map_preimage]
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_chainMap (x := moduleHeartVertex S M)
    (y := moduleHeartVertex S N) ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.moduleFreeCochainResolution S).map f)).symm

/-- 概要：J の H⁰ 同型は加群の射をそのまま復元する。
方針：辺のホモロジー比較と D5b の増大射の自然性を合成する。
規約：順方向は J.map。使われ方：Hom 全単射と H⁰ の両立。 -/
lemma moduleHeartHZeroIso_naturality {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroFunctor S).map ((moduleHeartFunctor S).map f) ≫
      (moduleHeartHZeroIso S N).hom = (moduleHeartHZeroIso S M).hom ≫ f := by
  rw [moduleHeartFunctor_map_edge]
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroMap S _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedChainMapEdge_hZero, Category.assoc, Category.assoc,
    moduleFreeCochainHomologyZeroIso_naturality]

/-- 概要：J の後で H⁰ を取ると恒等関手に自然に同型である。
方針：各加群の D5b の比較とその自然性をまとめる。
規約：成分は moduleHeartHZeroIso。使われ方：heart と加群圏の同定。 -/
def moduleHeartHZeroNatIso :
    moduleHeartFunctor S ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroFunctor S ≅ 𝟭 (ModuleCat.{u} S) :=
  NatIso.ofComponents (moduleHeartHZeroIso S) (moduleHeartHZeroIso_naturality S)

/-- 概要：Hom 全単射で送った射を H⁰ によって読むと元の射に戻る。
方針：J の H⁰ の自然性を Hom 同値の順方向で述べる。
規約：比較は D5b の増大同型。使われ方：heart の射の具体的計算。 -/
lemma moduleHeartHomEquiv_hZero {M N : ModuleCat.{u} S} (f : M ⟶ N) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHZeroFunctor S).map (moduleHeartHomEquiv S M N f) ≫
      (moduleHeartHZeroIso S N).hom = (moduleHeartHZeroIso S M).hom ≫ f :=
  moduleHeartHZeroIso_naturality S f

end SerrePositivity.InfinityCategories.Project.DerivedCategories
