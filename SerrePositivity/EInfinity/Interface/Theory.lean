module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import SerrePositivity.EInfinity.Interface.Core
public import SerrePositivity.EInfinity.Interface.StrictInputs
public import SerrePositivity.EInfinity.Interface.CoproductTensorLegs
public import SerrePositivity.InfinityCategories.Derived.BaseChange
public import SerrePositivity.InfinityCategories.Derived.Tensor.Fixed
public import SerrePositivity.InfinityCategories.F1B.Adjunction.Adjunction
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluation
public import SerrePositivity.InfinityCategories.Core.CatInfinity.NativeConeLeg
public import SerrePositivity.InfinityCategories.F2.Presentable.Definition
public import SerrePositivity.InfinityCategories.F2.Presentable.SiftedColimitPreservation
public import SerrePositivity.InfinityCategories.Stable.BinaryCoproductCocone

/-!
# BS が使う E∞ 代数の界面

## 概要
HA §3.2.2–3.2.4 の忘却と余極限、零次環、係数変更、厳密な入力の実現を指定する。
DAG XIII Construction 2.2.6 の冪作用は半線形な変換で受け取る。

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
open SerrePositivity.InfinityCategories.HomotopyLimits
open scoped Simplicial
namespace SerrePositivity.EInfinity

attribute [local instance] HasDerivedCategory.standard

/-- 指定関手が誘導する通常のホモトピー圏上の関手。 -/
abbrev hoMap {X Y : SSet.{u}} (F : X ⟶ Y) := (hoFunctor.map F).toFunctor

/-- 余鎖次数 i のホモロジーを通常のホモトピー圏上で取る。 -/
abbrev cohomologyOnHo (S : Type u) [CommRing S] (i : ℤ) :=
  (homotopyCategoryBridge (derivedInfinityCategory S)).inverse ⋙
    derivedInfinityHomologyFunctor S i

/-- 係数制限で比較するホモロジーの台の可換群。 -/
abbrev additiveCohomologyOnHo (S : Type u) [CommRing S] (i : ℤ) :=
  cohomologyOnHo S i ⋙ forget₂ (ModuleCat S) AddCommGrpCat

/-- 通常の代数の係数制限。 -/
abbrev restrictRingAlgebra {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    RingAlgebra T ⥤ RingAlgebra S :=
  Under.map (CommRingCat.ofHom f)

/-- 離散代数の余単体的図式。 -/
abbrev CosimplicialRingAlgebra (S : Type u) [CommRing S] :=
  CosimplicialObject (RingAlgebra S)

/-- 余単体的可換 dg 代数。 -/
abbrev CosimplicialCDGA (S : Type u) [CommRing S] :=
  CosimplicialObject (CommMon (Complex S))

/-- 交代余面複体を整数次数に零延長する。 -/
def cosimplicialCochains (S : Type u) [CommRing S] :
    CosimplicialRingAlgebra S ⥤ Complex S :=
  (Functor.whiskeringRight SimplexCategory _ _).obj (discreteAlgebraModule S) ⋙
    AlgebraicTopology.alternatingCofaceMapComplex (ModuleCat S) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (ModuleCat S)

/-- 通常の圏からその nerve のホモトピー圏への標準関手。 -/
def ordinaryToHoNerve (A : Type (u + 1)) [Category.{u} A] :
    A ⥤ (nerve A).HomotopyCategory where
  obj x := SSet.HomotopyCategory.mk (nerveEquiv.symm x)
  map f := SSet.HomotopyCategory.homMk (nerve.edgeMk f)
  map_id x := by
    rw [nerve.edgeMk_id]
    exact SSet.HomotopyCategory.homMk_id (X := nerve A) (nerveVertex x)
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
  { c : JoinCone D // c.vertex = x ∧ IsLimitCone c }

/-- BS 著者版 §7–8 に必要な E∞ 代数のデータと比較。 -/
structure EInfinityTheory extends EInfinityCore.{u} where
  forget_conservative (S : Type u) [CommRing S]
      {x y : (CAlg S) _⦋0⦌} (e : SSet.Edge x y) :
    IsInvertibleEdge (e.map (forget S)).toTruncated → IsInvertibleEdge e.toTruncated
  forget_preservesSifted (S : Type u) [CommRing S] :
    PreservesSmallSiftedColimits (forget S)
  presentable (S : Type u) [CommRing S] :
    @F2.Presentable.IsPresentable (CAlg S) (quasicategory S)
  coprodWith (S : Type u) [CommRing S] (y : (CAlg S) _⦋0⦌) : CAlg S ⟶ CAlg S
  coprodWith_cocone (S : Type u) [CommRing S] (x y : (CAlg S) _⦋0⦌) :
    { c : JoinCocone (binaryPointDiagram x y) //
      c.vertex = atVertex (coprodWith S y) x ∧ IsColimitCone c }
  coproduct_tensor (S : Type u) [CommRing S] (y : (CAlg S) _⦋0⦌) :
    FunctorIso (coprodWith S y ≫ forget S) (forget S ≫ tensorWith (atVertex (forget S) y))
  discrete_initial (S : Type u) [CommRing S] :
    letI := quasicategory S
    IsInitialVertex (atVertex (discrete S)
      (nerveVertex (Under.mk (𝟙 (CommRingCat.of S)))))

  /-- HA 3.2.4.7 の全関手版の同型と、指定された余積錐の二脚との適合性。 -/
  coproduct_tensor_legs (S : Type u) [CommRing S] (x y : (CAlg S) _⦋0⦌) :
    TensorCoproductLegCompatibility S toEInfinityCore x y (coprodWith S y)
      (coprodWith_cocone S x y).val (coprodWith_cocone S x y).property.1 (coproduct_tensor S y)

  restrictD {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    derivedInfinityCategory T ⟶ derivedInfinityCategory S
  restrictD_id (S : Type u) [CommRing S] :
    FunctorIso (restrictD (RingHom.id S)) (𝟙 (derivedInfinityCategory S))
  restrictD_comp {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
      (f : S →+* T) (g : T →+* W) :
    FunctorIso (restrictD (g.comp f)) (restrictD g ≫ restrictD f)
  /-- DAG XIII Construction 2.2.6 の半線形作用を読むための自然比較。 -/
  restrictD_homologyIso {S T : Type u} [CommRing S] [CommRing T]
      (f : S →+* T) (i : ℤ) :
    hoMap (restrictD f) ⋙ additiveCohomologyOnHo S i ≅ additiveCohomologyOnHo T i
  restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    CAlg T ⟶ CAlg S
  baseChange {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    CAlg S ⟶ CAlg T
  baseChange_adjunction {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    @QCatAdjunction (CAlg S) (CAlg T) (quasicategory S) (quasicategory T)
      (baseChange f) (restrict f)
  restrict_forget {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    FunctorIso (restrict f ≫ forget S) (forget T ≫ restrictD f)
  baseChange_forget {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    FunctorIso (baseChange f ≫ forget T) (forget S ≫ derivedInfinityBaseChange f)
  restrict_id (S : Type u) [CommRing S] :
    FunctorIso (restrict (RingHom.id S)) (𝟙 (CAlg S))
  restrict_comp {S T W : Type u} [CommRing S] [CommRing T] [CommRing W]
      (f : S →+* T) (g : T →+* W) :
    FunctorIso (restrict (g.comp f)) (restrict g ≫ restrict f)
  discrete_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    FunctorIso (nerveMap (restrictRingAlgebra f) ≫ discrete S) (discrete T ≫ restrict f)

  pi0 (S : Type u) [CommRing S] : (CAlg S).HomotopyCategory ⥤ RingAlgebra S
  pi0_forget (S : Type u) [CommRing S] :
    pi0 S ⋙ discreteAlgebraModule S ≅ hoMap (forget S) ⋙ cohomologyOnHo S 0
  pi0_discrete (S : Type u) [CommRing S] :
    ordinaryToHoNerve (RingAlgebra S) ⋙ hoMap (discrete S) ⋙ pi0 S ≅
      𝟭 (RingAlgebra S)
  pi0_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    hoMap (restrict f) ⋙ pi0 S ≅ pi0 T ⋙ restrictRingAlgebra f

  strictToD (S : Type u) [CommRing S] : nerve (Complex S) ⟶ derivedInfinityCategory S
  /-- BS 著者版 Theorem 6.2 の Tot で使う、厳密複体のホモロジーとの自然比較。 -/
  strictToD_homologyIso (S : Type u) [CommRing S] (i : ℤ) :
    ordinaryToHoNerve (Complex S) ⋙ hoMap (strictToD S) ⋙ cohomologyOnHo S i ≅
      HomologicalComplex.homologyFunctor (ModuleCat S) (.up ℤ) i
  ofCosimplicial (S : Type u) [CommRing S] : nerve (CosimplicialRingAlgebra S) ⟶ CAlg S
  ofCosimplicial_forget (S : Type u) [CommRing S] :
    FunctorIso (ofCosimplicial S ≫ forget S)
      (nerveMap (cosimplicialCochains S) ≫ strictToD S)
  ofCosimplicial_cone (S : Type u) [CommRing S] (X : CosimplicialRingAlgebra S) :
    TotalizationCone (cosimplicialNerve X ≫ discrete S)
      (atVertex (ofCosimplicial S) (nerveVertex X))
  ofCosimplicial_restrict {S T : Type u} [CommRing S] [CommRing T] (f : S →+* T) :
    FunctorIso
      (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (restrictRingAlgebra f)) ≫
        ofCosimplicial S)
      (ofCosimplicial T ≫ restrict f)
  ofCdga (S : Type u) [CommRing S] : nerve (CommMon (Complex S)) ⟶ CAlg S
  ofCdga_forget (S : Type u) [CommRing S] :
    FunctorIso (ofCdga S ≫ forget S) (nerveMap (CommMon.forget (Complex S)) ≫ strictToD S)
  ofCdga_discrete (S : Type u) [CommRing S] :
    FunctorIso (nerveMap (discreteCDGA S) ≫ ofCdga S) (discrete S)
  ofCosimplicialCdga (S : Type u) [CommRing S] : nerve (CosimplicialCDGA S) ⟶ CAlg S
  ofCosimplicialCdga_cone (S : Type u) [CommRing S] (X : CosimplicialCDGA S) :
    TotalizationCone (cosimplicialNerve X ≫ ofCdga S)
      (atVertex (ofCosimplicialCdga S) (nerveVertex X))
  ofCosimplicialCdga_discrete (S : Type u) [CommRing S] :
    FunctorIso
      (nerveMap ((Functor.whiskeringRight SimplexCategory _ _).obj (discreteCDGA S)) ≫
        ofCosimplicialCdga S) (ofCosimplicial S)
  ofCosimplicialCdga_evalZero (S : Type u) [CommRing S] :
    SSet.Homotopy (ofCosimplicialCdga S)
      (nerveMap ((evaluation SimplexCategory (CommMon (Complex S))).obj ⦋0⦌) ≫ ofCdga S)

  ofCosimplicialCdga_evalZero_leg (S : Type u) [CommRing S] (X : CosimplicialCDGA S) :
    (simplicialHomotopyVertexEdge (ofCosimplicialCdga_evalZero S) (nerveVertex X)).edge =
      (F2.nativeConeLeg (ofCosimplicialCdga_cone S X).val
        (ULift.up (nerveVertex (⦋0⦌ : SimplexCategory)))).edge

  powerOp0 (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p] :
    FunctorHom (forget k) (forget k ≫ restrictD (frobenius k p))
  powerOp0_zero (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (x : (CAlg k) _⦋0⦌) (a : ((pi0 k).obj (SSet.HomotopyCategory.mk x)).right) :
    let e := (pi0_forget k).app (SSet.HomotopyCategory.mk x)
    let α := (cohomologyOnHo k 0).map (functorHomEvaluate (powerOp0 k p) x)
    let res := (restrictD_homologyIso (frobenius k p) 0).app
      (SSet.HomotopyCategory.mk (atVertex (forget k) x))
    res.hom (α (e.hom a)) =
      e.hom (a ^ p)
  powerOp0_pos (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (x : (CAlg k) _⦋0⦌) (n : ℤ) (hn : 0 < n) :
    (cohomologyOnHo k (-n)).map (functorHomEvaluate (powerOp0 k p) x) = 0
  powerOp0_discrete (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (B : RingAlgebra k) (f : B ⟶ (restrictRingAlgebra (frobenius k p)).obj B)
      (hf : ∀ a : B.right, f.right.hom a = a ^ p) :
    letI := quasicategory k
    let x := atVertex (discrete k) (nerveVertex B)
    functorHomEvaluate (powerOp0 k p) x =
      SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map (discrete k ≫ forget k)) ≫
        (((discrete_restrict (frobenius k p)).app (nerveVertex B)).map (forget k)).hom ≫
        ((restrict_forget (frobenius k p)).app x).hom
  powerOp0_tot (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] [CharP k p]
      (X : CosimplicialRingAlgebra k)
      (f : X ⟶ X ⋙ restrictRingAlgebra (frobenius k p))
      (hf : ∀ j (a : (X.obj j).right), (f.app j).right.hom a = a ^ p) :
    letI := quasicategory k
    let x := atVertex (ofCosimplicial k) (nerveVertex X)
    functorHomEvaluate (powerOp0 k p) x =
      SSet.HomotopyCategory.homMk ((nerve.edgeMk f).map (ofCosimplicial k ≫ forget k)) ≫
        (((ofCosimplicial_restrict (frobenius k p)).app (nerveVertex X)).map (forget k)).hom ≫
        ((restrict_forget (frobenius k p)).app x).hom

/-- 自然比較の成分を台の加法同型として読む。 -/
def EInfinityTheory.restrictD_homology (E : EInfinityTheory.{u})
    {S T : Type u} [CommRing S] [CommRing T]
    (f : S →+* T) (i : ℤ) (x : (derivedInfinityCategory T) _⦋0⦌) :
    derivedInfinityHomology S i (atVertex (E.restrictD f) x) ≃+
      derivedInfinityHomology T i x :=
  ((E.restrictD_homologyIso f i).app (SSet.HomotopyCategory.mk x)).addCommGroupIsoToAddEquiv

end SerrePositivity.EInfinity
