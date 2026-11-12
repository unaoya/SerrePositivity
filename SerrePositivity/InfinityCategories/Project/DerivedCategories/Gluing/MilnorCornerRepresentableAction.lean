module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.MilnorFreeHomComponents
public import SerrePositivity.KST.SConstruction.DGPerfectRealization
/-!
概要：元 Milnor 四角形の下辺・上辺の代表延長作用を元の代数射へ照合する。
方針：公開の代表評価の自然性を使い、同じ閉同型と Yoneda 評価で正規化する。
規約：汎用の補助計算は非公開とし、元四角形の二辺だけを供給する。
使われ方：実自由 Hom の比較差の両成分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded KST.SConstruction
variable (R : Type u) [CommRing R] (B : Type v) [DGCategory R B] [Small.{u} B]
  (T : Type w) [DGCategory R T] [Small.{u} T] (F : DGFunctor R B T)
private lemma milnorCornerRepresentable_naturality (x y : B) :
    yonedaHom R B x y ≫ (dgModuleExtension R B T F).map
      (representable R x) (representable R y) ≫
      moduleHomPostcompose R T _ _ _ (dgModuleExtensionRepresentableIso R B T F y).hom =
    (F.map x y ≫ yonedaHom R T (F.obj x) (F.obj y)) ≫
      moduleHomPrecompose R T _ _ _
        (dgModuleExtensionRepresentableIso R B T F x).hom := by
  let K : DGFunctor R B (PerfectDGModule R T) :=
    { obj := fun a => dgRepresentablePerfectPoint R T (F.obj a)
      map := fun a b => F.map a b ≫ yonedaHom R T (F.obj a) (F.obj b)
      map_id := fun a => (F.comp (dgYoneda R T)).map_id a
      map_comp := fun a b c => (F.comp (dgYoneda R T)).map_comp a b c }
  have hk : dgPerfectRealizationKernel R B T K = functorGraph R B T F := by
    apply EnrichedFunctor.ext (Complex R)
    case h_obj => intro a; rfl
    intro a b
    simp only [eqToHom_refl, Category.comp_id]
    change (F.map a b ≫ yonedaHom R T (F.obj a) (F.obj b)) ≫ 𝟙 _ = _
    exact Category.comp_id _
  have h := dgPerfectRealizationRepresentableIso_naturality R B T K x y
  let NatProperty (P : Bimodule R T B) : Prop :=
    yonedaHom R B x y ≫
      (BimoduleTensor.compose R T B (RightModule R B) P
        (DGFunctor.id _)).toFunctor.map (representable R x) (representable R y) ≫
      moduleHomPostcompose R T _ _ (P.obj y)
        (BimoduleTensor.rightUnitIso R T B P y).hom =
    P.map x y ≫ moduleHomPrecompose R T _ _ _
      (BimoduleTensor.rightUnitIso R T B P x).hom
  have ht : NatProperty (dgPerfectRealizationKernel R B T K) := h
  have ht' : NatProperty (functorGraph R B T F) := hk ▸ ht
  exact ht'
private def milnorCornerRepresentableHomIso (x y : B) :
    moduleHom R T ((dgModuleExtension R B T F).obj (representable R x))
      ((dgModuleExtension R B T F).obj (representable R y)) ≅
    moduleHom R T (representable R (F.obj x)) (representable R (F.obj y)) :=
  enrichedClosedIsoHomIso (Complex R)
    (dgModuleExtensionRepresentableIso R B T F x)
    (dgModuleExtensionRepresentableIso R B T F y)
private lemma milnorCornerRepresentable_conjugation (x y : B) :
    yonedaHom R B x y ≫ (dgModuleExtension R B T F).map
      (representable R x) (representable R y) ≫
      (milnorCornerRepresentableHomIso R B T F x y).hom =
    F.map x y ≫ yonedaHom R T (F.obj x) (F.obj y) := by
  let P : moduleHom R T (representable R (F.obj x)) (representable R (F.obj y)) ≅
      moduleHom R T ((dgModuleExtension R B T F).obj (representable R x))
        (representable R (F.obj y)) :=
    ((eHomFunctor (Complex R) («C» := ClosedCategory R (RightModule R T))).mapIso
      (dgModuleExtensionRepresentableIso R B T F x).op).app
        (ForgetEnrichment.of (Complex R) (representable R (F.obj y)))
  have hc : (milnorCornerRepresentableHomIso R B T F x y).hom ≫ P.hom =
      moduleHomPostcompose R T _ _ _
        (dgModuleExtensionRepresentableIso R B T F y).hom :=
    enrichedClosedIsoConjugation_naturality (Complex R)
      (dgModuleExtensionRepresentableIso R B T F x)
      (dgModuleExtensionRepresentableIso R B T F y)
  apply (cancel_mono P.hom).mp
  calc
    _ = yonedaHom R B x y ≫ (dgModuleExtension R B T F).map
        (representable R x) (representable R y) ≫ moduleHomPostcompose R T _ _ _
          (dgModuleExtensionRepresentableIso R B T F y).hom := by
      simp only [Category.assoc, hc]
    _ = _ := by
      have hp : P.hom = moduleHomPrecompose R T _ _ _
          (dgModuleExtensionRepresentableIso R B T F x).hom := rfl
      rw [hp]
      simpa only [Category.assoc] using milnorCornerRepresentable_naturality R B T F x y
private lemma milnorCornerRepresentable_evaluate (x y : B) :
    (dgModuleExtension R B T F).map (representable R x) (representable R y) ≫
      (milnorCornerRepresentableHomIso R B T F x y).hom ≫
      (dgYonedaIso R (F.obj x) (representable R (F.obj y))).hom =
    (dgYonedaIso R x (representable R y)).hom ≫ F.map x y := by
  have : IsIso (yonedaHom R B x y) := by
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  apply (cancel_epi (yonedaHom R B x y)).mp
  have h := congrArg (fun k => k ≫
    (dgYonedaIso R (F.obj x) (representable R (F.obj y))).hom)
    (milnorCornerRepresentable_conjugation R B T F x y)
  simp only [Category.assoc, yonedaHom, Iso.inv_hom_id_assoc, Iso.inv_hom_id,
    Category.comp_id] at h ⊢
  exact h
variable (d : DGOdotInput R)
def dgGluingMilnorLowerRepresentableHomIso (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) :
    moduleHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
      ((dgModuleExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower)).obj (representable R x))
      ((dgModuleExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower)).obj (representable R y)) ≅
    moduleHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
      (representable R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower).obj x))
      (representable R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower).obj y)) :=
  enrichedClosedIsoHomIso (Complex R)
    (dgModuleExtensionRepresentableIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) x)
    (dgModuleExtensionRepresentableIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) y)
lemma dgGluingMilnorLowerRepresentable_evaluate (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) :
    (dgModuleExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap
      R d.lower)).map
      (representable R x) (representable R y) ≫
      (dgGluingMilnorLowerRepresentableHomIso R d x y).hom ≫
      (dgYonedaIso R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower).obj x) (representable R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R
        d.lower).obj y))).hom =
    (dgYonedaIso R x (representable R y)).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower).map x y :=
  milnorCornerRepresentable_evaluate R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.left) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.lower) x y
def dgGluingMilnorUpperRepresentableHomIso (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) :
    moduleHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
      ((dgModuleExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)).obj (representable R x))
      ((dgModuleExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)).obj (representable R y)) ≅
    moduleHom R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
      (representable R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper).obj x))
      (representable R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper).obj y)) :=
  enrichedClosedIsoHomIso (Complex R)
    (dgModuleExtensionRepresentableIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper) x)
    (dgModuleExtensionRepresentableIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper) y)
lemma dgGluingMilnorUpperRepresentable_evaluate (x y : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) :
    (dgModuleExtension R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.corner)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper)).map
      (representable R x) (representable R y) ≫
      (dgGluingMilnorUpperRepresentableHomIso R d x y).hom ≫
      (dgYonedaIso R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper).obj x) (representable R ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R
        d.upper).obj y))).hom =
    (dgYonedaIso R x (representable R y)).hom ≫ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper).map x y :=
  milnorCornerRepresentable_evaluate R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R d.right) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R
    d.corner) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R d.upper) x y
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
