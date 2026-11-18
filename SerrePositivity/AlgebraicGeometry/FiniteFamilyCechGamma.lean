module

public import SerrePositivity.AlgebraicGeometry.FiniteFamilyCechDistribution
public import SerrePositivity.AlgebraicGeometry.SchemeGammaSigma

/-!
概要：元の有限族の nerve の切断を、同じ混合積の切断の積へ移す。
方針：標準射の同型と Γ の余積比較を、実際の関数環の積へ合成する。
規約：元の入射、単体の射、基底からの増大を保つ。
使われ方：同じ矩形タプルの Frobenius 係数の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry Opposite
universe u

/-- 小さい添字の環の積も、元の評価を射影に持つ関数環である。 -/
def smallCommRingPiIso {ι : Type} (A : ι → CommRingCat.{u}) :
    ∏ᶜ A ≅ CommRingCat.of (∀ i, A i) :=
  (productIsProduct A).conePointUniqueUpToIso
    (show IsLimit (Fan.mk (CommRingCat.of (∀ i, A i))
      (fun i ↦ CommRingCat.ofHom (Pi.evalRingHom _ i))) from
      { lift := fun s ↦ CommRingCat.ofHom (RingHom.pi (fun i ↦ (s.π.app ⟨i⟩).hom))
        fac := fun _ _ ↦ rfl
        uniq := fun _ _ h ↦ CommRingCat.hom_ext (DFunLike.ext _ _ (fun x ↦
          funext (fun i ↦ congrArg (fun g : _ ⟶ A i ↦ g x) (h ⟨i⟩)))) })

/-- 同じ関数環の評価は、元の圏論的な積の射影。 -/
theorem smallCommRingPiIso_eval {ι : Type} (A : ι → CommRingCat.{u}) (i : ι) :
    (smallCommRingPiIso A).hom ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) = Pi.π A i := by
  unfold smallCommRingPiIso
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)

variable {ι : Type} {S : Scheme.{u}} {Z : ι → Scheme.{u}} (f : ∀ i, Z i ⟶ S)

/-- 同じ有限族の元の nerve の切断と、元の各混合積の切断の積の標準同型。 -/
def finiteFamilyCechGammaIso [Finite ι] (n : SimplexCategory) :
    Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n))) ≅
      CommRingCat.of (∀ t : Fin (n.len + 1) → ι,
        Scheme.Γ.obj (op (finiteFamilyCechComponent f n t))) := by
  haveI := finiteFamilyCechMap_isIso f n.len
  exact Scheme.Γ.mapIso (asIso (finiteFamilyCechMap f n)).op ≪≫
    schemeGammaSigmaIso (fun t ↦ finiteFamilyCechComponent f n t) ≪≫
    smallCommRingPiIso (fun t ↦ Scheme.Γ.obj (op (finiteFamilyCechComponent f n t)))

set_option backward.isDefEq.respectTransparency false in
/-- 同じ成分での評価は、元の標準入射の Γ そのもの。 -/
theorem finiteFamilyCechGammaIso_eval [Finite ι] (n : SimplexCategory)
    (t : Fin (n.len + 1) → ι) :
    (finiteFamilyCechGammaIso f n).hom ≫ CommRingCat.ofHom (Pi.evalRingHom _ t) =
      Scheme.Γ.map (finiteFamilyCechInclusion f n t).op := by
  simp only [finiteFamilyCechGammaIso, Iso.trans_hom, Category.assoc,
    smallCommRingPiIso_eval, schemeGammaSigmaIso_π, Functor.mapIso_hom]
  change Scheme.Γ.map (finiteFamilyCechMap f n).op ≫
    Scheme.Γ.map (Sigma.ι _ t).op = _
  rw [← Scheme.Γ.map_comp, ← CategoryTheory.op_comp]
  rw [finiteFamilyCechMap, Sigma.ι_comp_desc]

set_option backward.isDefEq.respectTransparency false in
/-- 単体の射への同じ係数比較の自然性を、元の各成分で照合する。 -/
theorem finiteFamilyCechGammaIso_naturality [Finite ι] {m n : SimplexCategory}
    (a : m ⟶ n) (t : Fin (n.len + 1) → ι) :
    Scheme.Γ.map ((Arrow.mk (Sigma.desc f)).cechNerve.map a.op).op ≫
        (finiteFamilyCechGammaIso f n).hom ≫
        CommRingCat.ofHom (Pi.evalRingHom _ t) =
      (finiteFamilyCechGammaIso f m).hom ≫
        CommRingCat.ofHom (Pi.evalRingHom _ (fun j ↦ t (a.toOrderHom j))) ≫
        Scheme.Γ.map (finiteFamilyCechComponentMap f a t).op := by
  rw [finiteFamilyCechGammaIso_eval, ← Category.assoc,
    finiteFamilyCechGammaIso_eval, ← Scheme.Γ.map_comp,
    ← Scheme.Γ.map_comp, ← CategoryTheory.op_comp, ← CategoryTheory.op_comp,
    finiteFamilyCechInclusion_naturality]

set_option backward.isDefEq.respectTransparency false in
/-- 元の基底からの増大は、同じ混合積の元の基底写像へ移る。 -/
theorem finiteFamilyCechGammaIso_augmentation [Finite ι] (n : SimplexCategory)
    (t : Fin (n.len + 1) → ι) :
    Scheme.Γ.map (WidePullback.base
        (fun _ : Fin (n.len + 1) ↦ Sigma.desc f)).op ≫
        (finiteFamilyCechGammaIso f n).hom ≫
        CommRingCat.ofHom (Pi.evalRingHom _ t) =
      Scheme.Γ.map (WidePullback.base (fun j ↦ f (t j))).op := by
  rw [finiteFamilyCechGammaIso_eval, ← Scheme.Γ.map_comp,
    ← CategoryTheory.op_comp, finiteFamilyCechInclusion_base]

set_option backward.isDefEq.respectTransparency false in
/-- 元の nerve の Γ を、同じ成分の関数環へ標準比較で移した余単体環。 -/
def finiteFamilyCechGammaDiagram [Finite ι] : CosimplicialObject CommRingCat.{u} where
  obj n := CommRingCat.of (∀ t : Fin (n.len + 1) → ι,
    Scheme.Γ.obj (op (finiteFamilyCechComponent f n t)))
  map {m n} a := (finiteFamilyCechGammaIso f m).inv ≫
    Scheme.Γ.map ((Arrow.mk (Sigma.desc f)).cechNerve.map a.op).op ≫
    (finiteFamilyCechGammaIso f n).hom
  map_id n := by
    change (finiteFamilyCechGammaIso f n).inv ≫
      (((Arrow.mk (Sigma.desc f)).cechNerve.rightOp ⋙ Scheme.Γ).map (𝟙 n)) ≫
      (finiteFamilyCechGammaIso f n).hom = _
    rw [CategoryTheory.Functor.map_id]
    change (finiteFamilyCechGammaIso f n).inv ≫
      (𝟙 (Scheme.Γ.obj (op ((Arrow.mk (Sigma.desc f)).cechNerve.obj (op n))))) ≫
      (finiteFamilyCechGammaIso f n).hom = _
    simp only [Category.id_comp, Iso.inv_hom_id]
  map_comp a b := by
    simp only [CategoryTheory.Functor.map_comp, op_comp, Category.assoc,
      Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- 同じ余単体環の射は、元のタプルの再添字付けと元の成分の Γ。 -/
theorem finiteFamilyCechGammaDiagram_map_eval [Finite ι] {m n : SimplexCategory}
    (a : m ⟶ n) (t : Fin (n.len + 1) → ι) :
    (finiteFamilyCechGammaDiagram f).map a ≫ CommRingCat.ofHom (Pi.evalRingHom _ t) =
      CommRingCat.ofHom (Pi.evalRingHom _ (fun j ↦ t (a.toOrderHom j))) ≫
        Scheme.Γ.map (finiteFamilyCechComponentMap f a t).op := by
  change ((finiteFamilyCechGammaIso f m).inv ≫
    Scheme.Γ.map ((Arrow.mk (Sigma.desc f)).cechNerve.map a.op).op ≫
      (finiteFamilyCechGammaIso f n).hom) ≫ _ = _
  simp only [Category.assoc]
  rw [finiteFamilyCechGammaIso_naturality, Iso.inv_hom_id_assoc]

/-- 全ての単体の射を保つ、元の nerve の Γ との同じ標準自然同型。 -/
def finiteFamilyCechGammaDiagramIso [Finite ι] :
    (Arrow.mk (Sigma.desc f)).cechNerve.rightOp ⋙ Scheme.Γ ≅
      finiteFamilyCechGammaDiagram f :=
  NatIso.ofComponents (finiteFamilyCechGammaIso f) (fun a ↦ by
    simp only [finiteFamilyCechGammaDiagram, Iso.hom_inv_id_assoc]
    rfl)

end SerrePositivity.AlgebraicGeometry
