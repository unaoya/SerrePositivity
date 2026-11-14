module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import SerrePositivity.KST.LocalizingInvariants.SpectrumHomotopyFunctor
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import SerrePositivity.EInfinity.Interface.PrimeField
public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.EInfinity.Interface.StrictInputs
public import SerrePositivity.EInfinity.Interface.CoproductTensorLegs
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Homotopies.HomotopyModels.BaseChange
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.Fixed
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.Adjunction
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.NativeConeLeg
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.BinaryCoproductCocone

/-!
# BS が使う E∞ 代数の界面

## 概要
HA §3.2.2–3.2.4 の忘却と余極限、零次環、係数変更、厳密な入力の実現を指定する。
May, Proposition 2.3 の P⁰ は ho(CAlg F_p) 上のホモトピー可換群の自然変換で受け取る。

## 方針
同じ忘却関手に対する自然比較を保持し、証明済みの中核に残りのデータを加える。

## 規約
Hⁱ は余鎖次数、πₙ は H⁻ⁿ とする。係数制限の D(S) 側の比較を共用する。

## 使われ方
BS 著者版 Construction 7.6、Definition 8.2、Lemma 8.4 と Proposition 8.13。
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories

open scoped _root_.Simplicial
namespace SerrePositivity.EInfinity

open _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories (derivedInfinityCategory)
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions (nerveVertex)

attribute [local instance] HasDerivedCategory.standard

/-- 指定関手が誘導する通常のホモトピー圏上の関手。 -/
abbrev hoMap {X Y : SSet.{u}} (F : X ⟶ Y) := (hoFunctor.map F).toFunctor

/-- 余鎖次数 i のホモロジーを通常のホモトピー圏上で取る。 -/
abbrev cohomologyOnHo (S : Type u) [CommRing S] (i : ℤ) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S)).inverse ⋙
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomologyFunctor S i

/-- 係数制限で比較するホモロジーの台の可換群。 -/
abbrev additiveCohomologyOnHo (S : Type u) [CommRing S] (i : ℤ) :=
  cohomologyOnHo S i ⋙ forget₂ (ModuleCat S) AddCommGrpCat

/-- 通常の代数の係数制限。 -/
abbrev restrictRingAlgebra {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    RingAlgebra T ⥤ RingAlgebra S :=
  Under.map (CommRingCat.ofHom f)

/-- 忘却した導来複体の H^{-n} を、ホモトピー次数 n の可換群として読む。 -/
abbrev homotopyGroupsOnHo (k : Type u) [CommRing k] {C : SSet.{u + 1}}
    (U : C ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory k)
    (n : ℤ) :=
  hoMap U ⋙ additiveCohomologyOnHo k (-n)

/-- 離散代数の余単体的図式。 -/
abbrev CosimplicialRingAlgebra (S : Type u) [CommRing S] :=
  CosimplicialObject (RingAlgebra S)

/-- 余単体的可換 dg 代数。 -/
abbrev CosimplicialCDGA (S : Type u) [CommRing S] :=
  CosimplicialObject (CommMon (Complex S))

/-- 交代余面複体を整数次数に零延長する。 -/
def cosimplicialCochains (S : Type u) [CommRing S] :
    CosimplicialRingAlgebra S ⥤ Complex S :=
  (Functor.whiskeringRight SimplexCategory _ _).obj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule S) ⋙
    AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat S) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat S)

/-- 通常の圏からその nerve のホモトピー圏への標準関手。 -/
def ordinaryToHoNerve (A : Type (u + 1)) [Category.{u} A] :
    A ⥤ (nerve A).HomotopyCategory where
  obj x := SSet.HomotopyCategory.mk (nerveEquiv.symm x)
  map f := SSet.HomotopyCategory.homMk (nerve.edgeMk f)
  map_id x := by
    rw [nerve.edgeMk_id]
    exact SSet.HomotopyCategory.homMk_id (X := nerve A) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x)
  map_comp f g := by
    obtain ⟨h⟩ := (nerve.nonempty_compStruct_iff f g (f ≫ g)).mpr rfl
    exact (SSet.HomotopyCategory.homMk_comp_homMk h).symm

/-- 小さい Δ の nerve から指定した大きい圏への厳密な図式。 -/
def cosimplicialNerve {A : Type w} [Category.{v} A]
    (F : CosimplicialObject A) :
    (SSet.uliftFunctor.{max v w, 0}).obj (nerve SimplexCategory) ⟶ nerve A where
  app _ := ↾fun q => (F.mapComposableArrows _).obj q.down
  naturality _ _ _ := rfl

/-- 指定関手の頂点を頂点に持つ Δ 上の極限錐。 -/
abbrev TotalizationCone {X : SSet.{u + 1}}
    (D : (SSet.uliftFunctor.{u + 1, 0}).obj (nerve SimplexCategory) ⟶ X) (x : X _⦋0⦌) :=
  { c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone D // c.vertex = x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone c }

/-- BS 著者版 §7–8 に必要な E∞ 代数のデータと比較。 -/
structure EInfinityTheory extends EInfinityCore.{u} where
  forget_conservative (S : Type u) [CommRing S]
      {x y : (CAlg S) _⦋0⦌} (e : SSet.Edge x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (e.map (forget S)).toTruncated → _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge e.toTruncated
  forget_preservesSifted (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PreservesSmallSiftedColimits (forget S)
  presentable (S : Type u) [CommRing S] :
    @_root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (CAlg S) (quasicategory S)
  coprodWith (S : Type u) [CommRing S] (y : (CAlg S) _⦋0⦌) : CAlg S ⟶ CAlg S
  coprodWith_cocone (S : Type u) [CommRing S] (x y : (CAlg S) _⦋0⦌) :
    { c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.binaryPointDiagram x y) //
      c.vertex = atVertex (coprodWith S y) x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c }
  coproduct_tensor (S : Type u) [CommRing S] (y : (CAlg S) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (coprodWith S y ≫ forget S) (forget S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.tensorWith (atVertex (forget S) y))
  discrete_initial (S : Type u) [CommRing S] :
    letI := quasicategory S
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex (atVertex (discrete S)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Under.mk (𝟙 (CommRingCat.of S)))))

  /-- HA 3.2.4.7 の全関手版の同型と、指定された余積錐の二脚との適合性。 -/
  coproduct_tensor_legs (S : Type u) [CommRing S] (x y : (CAlg S) _⦋0⦌) :
    TensorCoproductLegCompatibility S toEInfinityCore x y (coprodWith S y)
      (coprodWith_cocone S x y).val (coprodWith_cocone S x y).property.1 (coproduct_tensor S y)

  restrictD {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory T ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S
  restrictD_id (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (restrictD (RingHom.id S)) (𝟙 (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S))
  restrictD_comp {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
      (f : S →+* T) (g : T →+* W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (restrictD (g.comp f)) (restrictD g ≫ restrictD f)
  /-- DAG XIII Construction 2.2.6 の半線形作用を読むための自然比較。 -/
  restrictD_homologyIso {S T : Type u} [CommRing S] [CommRing T]
      (f : S →+* T) (i : ℤ) :
    hoMap (restrictD f) ⋙ additiveCohomologyOnHo S i ≅ additiveCohomologyOnHo T i
  restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    CAlg T ⟶ CAlg S
  baseChange {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    CAlg S ⟶ CAlg T
  baseChange_adjunction {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.QCatAdjunction (CAlg S) (CAlg T) (quasicategory S) (quasicategory T)
      (baseChange f) (restrict f)
  restrict_forget {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (restrict f ≫ forget S) (forget T ≫ restrictD f)
  baseChange_forget {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (baseChange f ≫ forget T) (forget S ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityBaseChange f)
  restrict_id (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (restrict (RingHom.id S)) (𝟙 (CAlg S))
  restrict_comp {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
      (f : S →+* T) (g : T →+* W) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (restrict (g.comp f)) (restrict g ≫ restrict f)
  discrete_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (restrictRingAlgebra f) ≫ discrete S) (discrete T ≫ restrict f)

  pi0 (S : Type u) [CommRing S] : (CAlg S).HomotopyCategory ⥤ RingAlgebra S
  pi0_forget (S : Type u) [CommRing S] :
    pi0 S ⋙ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.discreteAlgebraModule S ≅ hoMap (forget S) ⋙ cohomologyOnHo S 0
  pi0_discrete (S : Type u) [CommRing S] :
    ordinaryToHoNerve (RingAlgebra S) ⋙ hoMap (discrete S) ⋙ pi0 S ≅
      𝟭 (RingAlgebra S)
  pi0_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    hoMap (restrict f) ⋙ pi0 S ≅ pi0 T ⋙ restrictRingAlgebra f

  strictToD (S : Type u) [CommRing S] : nerve (Complex S) ⟶ _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S
  /-- BS 著者版 Theorem 6.2 の Tot で使う、厳密複体のホモロジーとの自然比較。 -/
  strictToD_homologyIso (S : Type u) [CommRing S] (i : ℤ) :
    ordinaryToHoNerve (Complex S) ⋙ hoMap (strictToD S) ⋙ cohomologyOnHo S i ≅
      HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i
  ofCosimplicial (S : Type u) [CommRing S] : nerve (CosimplicialRingAlgebra S) ⟶ CAlg S
  ofCosimplicial_forget (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (ofCosimplicial S ≫ forget S)
      (nerveMap (cosimplicialCochains S) ≫ strictToD S)
  ofCosimplicial_cone (S : Type u) [CommRing S] (X : CosimplicialRingAlgebra S) :
    TotalizationCone (cosimplicialNerve X ≫ discrete S)
      (atVertex (ofCosimplicial S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
  ofCosimplicial_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (restrictRingAlgebra f)) ≫
        ofCosimplicial S)
      (ofCosimplicial T ≫ restrict f)
  ofCdga (S : Type u) [CommRing S] : nerve (CommMon (Complex S)) ⟶ CAlg S
  ofCdga_forget (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (ofCdga S ≫ forget S) (nerveMap (CommMon.forget (Complex S)) ≫ strictToD S)
  ofCdga_discrete (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (nerveMap (discreteCDGA S) ≫ ofCdga S) (discrete S)
  ofCosimplicialCdga (S : Type u) [CommRing S] : nerve (CosimplicialCDGA S) ⟶ CAlg S
  ofCosimplicialCdga_cone (S : Type u) [CommRing S] (X : CosimplicialCDGA S) :
    TotalizationCone (cosimplicialNerve X ≫ ofCdga S)
      (atVertex (ofCosimplicialCdga S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X))
  ofCosimplicialCdga_discrete (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (discreteCDGA S)) ≫
        ofCosimplicialCdga S) (ofCosimplicial S)
  ofCosimplicialCdga_evalZero (S : Type u) [CommRing S] :
    SSet.Homotopy (ofCosimplicialCdga S)
      (nerveMap ((evaluation SimplexCategory (CommMon (Complex S))).obj ⦋0⦌) ≫ ofCdga S)

  ofCosimplicialCdga_evalZero_leg (S : Type u) [CommRing S] (X : CosimplicialCDGA S) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.simplicialHomotopyVertexEdge (ofCosimplicialCdga_evalZero S) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex X)).edge =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.nativeConeLeg (ofCosimplicialCdga_cone S X).val
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (⦋0⦌ : SimplexCategory)))).edge

  /-- D79：同じ導来圏から実際の Ω スペクトルの準圏への忘却。 -/
  toSpectra (S : Type u) [CommRing S] :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory S ⟶
      SerrePositivity.KST.Spectra.Sp.{u}
  /-- 係数制限は台のスペクトルを変えない。 -/
  toSpectra_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (restrictD f ≫ toSpectra S) (toSpectra T)
  /-- スペクトルの整数 π と複体の H の、射に自然な比較。 -/
  toSpectra_homologyIso (S : Type u) [CommRing S] (i : ℤ) :
    hoMap (toSpectra S) ⋙
      SerrePositivity.KST.LocalizingInvariants.SpectrumHo.piFunctor (-i) ⋙
        CommGrpCat.toAddCommGrp ≅ additiveCohomologyOnHo S i
  /-- D79 改訂：素体上の全整数次数の P⁰。coherent な Sp 値の出力は要求しない。 -/
  powerOp0 (p : ℕ) [Fact p.Prime] (n : ℤ) :
    homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n ⟶
      homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n
  powerOp0_zero (p : ℕ) [Fact p.Prime]
      (x : (CAlg (EInfinityPrimeField.{u} p)) _⦋0⦌)
      (a : ((pi0 (EInfinityPrimeField.{u} p)).obj (SSet.HomotopyCategory.mk x)).right) :
    let e := (pi0_forget (EInfinityPrimeField.{u} p)).app (SSet.HomotopyCategory.mk x)
    (powerOp0 p 0).app (SSet.HomotopyCategory.mk x) (e.hom a) = e.hom (a ^ p)
  powerOp0_pos (p : ℕ) [Fact p.Prime]
      (x : (CAlg (EInfinityPrimeField.{u} p)) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
    (powerOp0 p n).app (SSet.HomotopyCategory.mk x) = 0
  powerOp0_discrete (p : ℕ) [Fact p.Prime]
      (B : RingAlgebra (EInfinityPrimeField.{u} p)) (f : B ⟶ B)
      (hf : ∀ a : B.right, f.right.hom a = a ^ p) (n : ℤ) :
    let x := atVertex (discrete (EInfinityPrimeField.{u} p)) (nerveVertex B)
    (powerOp0 p n).app (SSet.HomotopyCategory.mk x) =
      (homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n).map
        (SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map (discrete (EInfinityPrimeField.{u} p))))
  powerOp0_tot (p : ℕ) [Fact p.Prime]
      (X : CosimplicialRingAlgebra (EInfinityPrimeField.{u} p)) (f : X ⟶ X)
      (hf : ∀ j (a : (X.obj j).right), (f.app j).right.hom a = a ^ p) (n : ℤ) :
    let x := atVertex (ofCosimplicial (EInfinityPrimeField.{u} p)) (nerveVertex X)
    (powerOp0 p n).app (SSet.HomotopyCategory.mk x) =
      (homotopyGroupsOnHo (EInfinityPrimeField.{u} p) (forget (EInfinityPrimeField.{u} p)) n).map
        (SSet.HomotopyCategory.homMk
          ((nerve.edgeMk f).map (ofCosimplicial (EInfinityPrimeField.{u} p))))

/-- 自然比較の成分を台の加法同型として読む。 -/
def EInfinityTheory.restrictD_homology (E : EInfinityTheory.{u})
    {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (i : ℤ) (x : (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.derivedInfinityCategory T) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology S i (atVertex (E.restrictD f) x) ≃+
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomology T i x :=
  ((E.restrictD_homologyIso f i).app (SSet.HomotopyCategory.mk x)).addCommGroupIsoToAddEquiv

end SerrePositivity.EInfinity
