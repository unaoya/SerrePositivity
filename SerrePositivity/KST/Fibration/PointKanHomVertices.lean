module
public import SerrePositivity.InfinityCategories.F1.KanPointHomNaturality

/-! # 一点からの標準 Hom 同型の零単体は、元の Yoneda 点をそのまま回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- Kan 豊穣圏の元の射の零単体は、同じ underlying 射の関手頂点。 -/
theorem kanObject_homEquiv'_functorVertex (K L : KanObject.{u}) (f : K ⟶ L) :
    SimplicialCategory.homEquiv' K L f = functorVertex (show K.obj ⟶ L.obj from f) := rfl

/-- 一点からの標準 Hom 同型は、元の通常の射の頂点をその Yoneda 点へ送る。 -/
theorem pointKanObjectHomIso_hom_vertex (K : KanObject.{u}) (f : pointKanObject ⟶ K) :
    (pointKanObjectHomIso K).hom.app (Opposite.op ⦋0⦌) (functorVertex f) =
      SSet.yonedaEquiv f := by
  have h := pointKanObjectHomNatIso.hom.naturality f
  rw [kanObject_sHomWhiskerLeft] at h
  have he := congrArg (fun m => m.app (Opposite.op ⦋0⦌)
    (functorVertex (show pointKanObject ⟶ pointKanObject from 𝟙 _))) h
  change (pointKanObjectHomIso K).hom.app (Opposite.op ⦋0⦌) (functorVertex (𝟙 _ ≫ f)) =
    f.app (Opposite.op ⦋0⦌) ((pointKanObjectHomIso pointKanObject).hom.app
      (Opposite.op ⦋0⦌) (functorVertex (show pointKanObject ⟶ pointKanObject from 𝟙 _))) at he
  let z : pointKanObject.obj _⦋0⦌ := SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u}))
  have hz : (pointKanObjectHomIso pointKanObject).hom.app (Opposite.op ⦋0⦌)
      (functorVertex (show pointKanObject ⟶ pointKanObject from 𝟙 _)) =
        z := by
    apply stdSimplex.ext
    intro i
    exact @Subsingleton.elim (Fin 1) inferInstance _ _
  rw [Category.id_comp, hz] at he
  change (pointKanObjectHomIso K).hom.app (Opposite.op ⦋0⦌) (functorVertex f) =
    SSet.yonedaEquiv f at he
  exact he

/-- 同じ標準 Hom 同型の逆は、元の点の同じ Yoneda 射の関手頂点。 -/
theorem pointKanObjectHomIso_inv_vertex (K : KanObject.{u}) (v : K.obj _⦋0⦌) :
    (pointKanObjectHomIso K).inv.app (Opposite.op ⦋0⦌) v =
      functorVertex (show pointKanObject ⟶ K from SSet.yonedaEquiv.symm v) := by
  apply (ConcreteCategory.bijective_of_isIso ((pointKanObjectHomIso K).hom.app
    (Opposite.op ⦋0⦌))).1
  have h := congrArg (fun m => m.app (Opposite.op ⦋0⦌) v) (pointKanObjectHomIso K).inv_hom_id
  change (pointKanObjectHomIso K).hom.app (Opposite.op ⦋0⦌)
    ((pointKanObjectHomIso K).inv.app (Opposite.op ⦋0⦌) v) = v at h
  rw [h, pointKanObjectHomIso_hom_vertex, Equiv.apply_symm_apply]

end SerrePositivity.KST.Fibration
