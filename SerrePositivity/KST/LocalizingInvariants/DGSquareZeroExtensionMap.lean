module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroExtensionLayerInclusion
public import SerrePositivity.KST.LocalizingInvariants.CochainCoconeBiprodMap
public import SerrePositivity.KST.LocalizingInvariants.CochainSplitCoconeNaturality
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraHomotopyPullbackMapCocone
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroMapOver

/-!
概要：平方零 class の元の可換正方形に沿う模型射は、元の層包含を保つ。
方針：実 cocone 模型射と元の短完全列の包含の自然性を、同じ複体同型で移す。
規約：底変更と元の係数射を明示。使われ方：層同型の自然性と像因子分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A A' W W' : Mon (Complex R)}
  (N : Bimod A A) (N' : Bimod A' A')
  (a : W ⟶ SquareZero.algebra A N) (a' : W' ⟶ SquareZero.algebra A' N')
  (w : W ⟶ W') (q : A ⟶ A') (b : SquareZero.algebra A N ⟶ SquareZero.algebra A' N')
  (t : N.X ⟶ N'.X) (hb : b.hom = biprod.map q.hom t) (h : w ≫ a' = a ≫ b)

include hb in
lemma map_zeroSection : SquareZero.zeroSection A N ≫ b = q ≫ SquareZero.zeroSection A' N' := by
  apply Mon.Hom.ext
  change biprod.inl ≫ b.hom = q.hom ≫ biprod.inl
  rw [hb, biprod.inl_map]

def map : model N a ⟶ model N' a' := DGAlgebra.HomotopyPullbackModel.map R a
  (SquareZero.zeroSection A N) a' (SquareZero.zeroSection A' N') w b q h
  (map_zeroSection N N' q b t hb).symm

def kernelMap : kernelComplex N ⟶ kernelComplex N' :=
  cochainNegInlCoconeMap q.hom t

lemma map_layerInclusion : layerInclusion N a ≫ (map N N' a a' w q b t hb h).hom =
    kernelMap N N' q t ≫ layerInclusion N' a' := by
  let e := DGAlgebra.HomotopyPullbackModel.complexIso R a (SquareZero.zeroSection A N)
  let e' := DGAlgebra.HomotopyPullbackModel.complexIso R a' (SquareZero.zeroSection A' N')
  have hf : a.hom ≫ b.hom = w.hom ≫ a'.hom :=
    (congrArg Mon.Hom.hom h).symm
  have hg : (-(SquareZero.zeroSection A N).hom) ≫ b.hom =
      q.hom ≫ (-(SquareZero.zeroSection A' N').hom) := by
    have hz : (SquareZero.zeroSection A N).hom ≫ b.hom =
        q.hom ≫ (SquareZero.zeroSection A' N').hom :=
      congrArg Mon.Hom.hom (map_zeroSection N N' q b t hb)
    simpa only [Preadditive.neg_comp, Preadditive.comp_neg] using congrArg Neg.neg hz
  let c := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (DGAlgebra.HomotopyPullbackModel.difference R a
    (SquareZero.zeroSection A N)) (DGAlgebra.HomotopyPullbackModel.difference R a'
    (SquareZero.zeroSection A' N')) (Limits.biprod.map w.hom q.hom)
    b.hom (cochainCoconeBiprodMap_comm _ _ _ _ _ _ _ hf hg)
  have hm : (map N N' a a' w q b t hb h).hom ≫ e'.hom = e.hom ≫ c :=
    DGAlgebra.HomotopyPullbackModel.map_toMappingCocone R _ _ _ _ _ _ _ _ _
  apply (cancel_mono e'.hom).1
  rw [Category.assoc, hm, ← Category.assoc]
  have he : layerInclusion N a ≫ e.hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a.hom (-(SquareZero.zeroSection A N).hom) :=
    layerInclusion_toCocone N a
  have he' : layerInclusion N' a' ≫ e'.hom =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a'.hom (-(SquareZero.zeroSection A' N').hom) :=
    layerInclusion_toCocone N' a'
  rw [he, Category.assoc, he']
  have hn := cochainCoconeBiprodInclusion_naturality _ _ _ _ _ _ _ hf hg
  have hk : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeMap (-(SquareZero.zeroSection A N).hom)
      (-(SquareZero.zeroSection A' N').hom) q.hom b.hom hg = kernelMap N N' q t := by
    unfold kernelMap cochainNegInlCoconeMap
    congr 1
  exact hn.trans (congrArg
    (fun k => k ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexMappingCoconeBiprodInclusion a'.hom
      (-(SquareZero.zeroSection A' N').hom)) hk)

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
