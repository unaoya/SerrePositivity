module
public import SerrePositivity.KST.SConstruction.PerfectDGExtension
public import SerrePositivity.DifferentialGraded.Derived.Functor

/-! # 射影的対象における graph 延長の実自然比較
概要：実 graph 延長と主導来延長を、元の射影的加群と全閉零射で自然に比較する。
方針：標準解像度の増大射を実延長で写し、射影的対象間の擬同型として反転する。
規約：任意の射影解像度を選び直さない。使われ方：実 Perf dg 関手の H⁰ 比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
private lemma map_eq_of_factorIso {C B : Type*} [Category* C] [Category* B]
    {G H : C ⥤ B} (e : G ≅ H) {X Y : C} (f g : X ⟶ Y)
    (h : G.map f = G.map g) : H.map f = H.map g := by
  apply (cancel_epi (e.hom.app X)).mp
  exact (e.hom.naturality f).symm.trans
    ((congrArg (fun k => k ≫ e.hom.app Y) h).trans (e.hom.naturality g))

variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

/-- 元の射影的対象への標準増大射の実 graph 延長は主導来圏で可逆。 -/
lemma projectiveGraphAugmentation_isIso (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    IsIso ((moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
      (moduleCanonicalProjectiveResolution A D M).π)) :=
  moduleToDerived_inverts A E _ (dgModuleExtension_projective_quasiIso A D E F
    (moduleCanonicalProjectiveResolution A D M).projective hM _
    (moduleCanonicalProjectiveResolution A D M).quasiIso)

/-- 元の射影的加群での、主導来延長から実 graph 延長への比較。 -/
def projectiveGraphComparison (M : ModuleCategory A D)
    (hM : moduleHomotopicallyProjective A D M) :
    (dgDerivedExtension A D E F).obj ((moduleToDerived A D).obj M) ≅
      (moduleToDerived A E).obj ((dgModuleExtension A D E F).onClosed.obj M) := by
  let := projectiveGraphAugmentation_isIso A D E F M hM
  exact dgResolutionDerivedExtensionComputation A D E F
    (moduleCanonicalProjectiveResolution A D) M ≪≫
      asIso ((moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
        (moduleCanonicalProjectiveResolution A D M).π))

/-- 増大射の自然性は、実 graph 延長後も主導来圏で可換。 -/
lemma graphResolutionAugmentation_naturality {M N : ModuleCategory A D} (f : M ⟶ N) :
    (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
        ((moduleCanonicalProjectiveResolution A D M).lift
          (moduleCanonicalProjectiveResolution A D N) f)) ≫
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
        (moduleCanonicalProjectiveResolution A D N).π) =
    (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map
        (moduleCanonicalProjectiveResolution A D M).π) ≫
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) := by
  let T := dgModuleExtension A D E F
  let R := moduleCanonicalProjectiveResolution A D
  have h := congrArg T.onHomotopy.map ((R M).lift_fac (R N) f)
  simp only [Functor.map_comp] at h
  change (moduleToHomotopy A E).map (T.onClosed.map ((R M).lift (R N) f)) ≫
      (moduleToHomotopy A E).map (T.onClosed.map (R N).π) =
    (moduleToHomotopy A E).map (T.onClosed.map (R M).π) ≫
      (moduleToHomotopy A E).map (T.onClosed.map f) at h
  have h' := congrArg (moduleHomotopyToDerivedClosed A E).map h
  simp only [← Functor.map_comp] at h'
  have he := map_eq_of_factorIso (moduleToHomotopyDerivedIso A E)
    (T.onClosed.map ((R M).lift (R N) f ≫ (R N).π))
    (T.onClosed.map ((R M).π ≫ f)) h'
  simpa only [Functor.map_comp] using he

/-- 射影的対象上の実比較は全ての元の閉零射について自然。 -/
lemma projectiveGraphComparison_naturality {M N : ModuleCategory A D}
    (hM : moduleHomotopicallyProjective A D M) (hN : moduleHomotopicallyProjective A D N)
    (f : M ⟶ N) :
    (dgDerivedExtension A D E F).map ((moduleToDerived A D).map f) ≫
      (projectiveGraphComparison A D E F N hN).hom =
    (projectiveGraphComparison A D E F M hM).hom ≫
      (moduleToDerived A E).map ((dgModuleExtension A D E F).onClosed.map f) := by
  change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
  dsimp only [dgDerivedExtension]
  rw [← Category.assoc, dgResolutionDerivedExtensionComputation_naturality]
  simp only [Category.assoc]
  exact congrArg (fun k =>
    (dgResolutionDerivedExtensionComputation A D E F
      (moduleCanonicalProjectiveResolution A D) M).hom ≫ k)
    (graphResolutionAugmentation_naturality A D E F f)

end SerrePositivity.KST.SConstruction
