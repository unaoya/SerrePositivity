module

public import SerrePositivity.KST.Comparison.GroupCompletionPathIdentity

/-!
# 標準群完備化写像の基点保存

概要：モノイドの単位は定数ループへ送られる。
方針：bar の単位の辺の定数性を全次数で確認し、区間上の評価で照合する。
規約：Segal 1974 Proposition 1.5、KST Lemma 2.13 の標準写像を用いる。
使われ方：K-L9 の点付きホモトピー類への接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Limits Opposite MonoidalCategory MonoidalClosed
open CartesianMonoidalCategory BraidedCategory
open scoped _root_.Simplicial
open SerrePositivity.SimplicialModel

/--
概要：単体的モノイドの全次数の単位からなる基点射。
方針：各次数で一を選び、モノイド射の単位保存で自然性を示す。
規約：定義域は直積圏の単位対象。
使われ方：元のモノイドの点付き対象化。
-/
def monoidUnitMap (M : SimplicialObject MonCat.{u}) : 𝟙_ SSet.{u} ⟶ monoidSpace M where
  app n := TypeCat.ofHom (fun _ => (1 : M.obj n))
  naturality {m n} f := by
    apply ConcreteCategory.hom_ext
    intro _
    exact (map_one (M.map f).hom).symm

/--
概要：単位と任意の区間の単体から作る bar の単体は基点に定数である。
方針：一対象圏の射列の各射を単位と照合する。
規約：元のモノイドに群状性は不要。
使われ方：群完備化写像の基点での区間評価。
-/
theorem monoidBarEdgeAt_unit (M : SimplicialObject MonCat.{u}) (n : ℕ)
    (t : (Δ[1] : SSet.{u}) _⦋n⦌) :
    monoidBarEdgeAt M n 1 t =
      (monoidBar M).map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op (monoidBarBasepoint M) := by
  have he : monoidEdgeSimplex (M.obj (op ⦋n⦌)) 1 =
      (Functor.const (Fin 2)).obj (SingleObj.star (M.obj (op ⦋n⦌))) :=
    ComposableArrows.ext₁ rfl rfl (by
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl)
  unfold monoidBarEdgeAt
  rw [he]
  refine ComposableArrows.ext (fun _ => rfl) ?_
  intro i hi
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (1 : M.obj (op ⦋n⦌)) =
    (M.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op).hom 1
  exact (map_one _).symm

/--
概要：単位でパラメータを固定すると標準 bar の辺写像は定数になる。
方針：単体ごとに単位の辺の式を適用する。
規約：全ての区間の単体を含む写像の等式。
使われ方：点付き内部 Hom の基点との照合。
-/
theorem monoidBarEdgeMap_unit (M : SimplicialObject MonCat.{u}) :
    monoidUnitMap M ▷ (Δ[1] : SSet.{u}) ≫ monoidBarEdgeMap M =
      SSet.const (monoidBarBasepoint M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro p
  exact monoidBarEdgeAt_unit M n.unop.len p.2

/--
概要：群完備化写像を区間へ制限し基礎指数へ含めると辺写像の curry になる。
方針：uncurry の単射性と標準写像の区間評価の式を使う。
規約：比較射を取り替えない。
使われ方：単位の像を定数ループと同定する。
-/
theorem monoidGroupCompletionMap_restriction_ι (M : SimplicialObject MonCat.{u}) :
    monoidGroupCompletionMap M ≫ loopPathRestriction (monoidBarKanPointed M) ≫
      PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval (monoidBarKanPointed M) =
        curry ((β_ (Δ[1] : SSet.{u}) (monoidSpace M)).hom ≫ monoidBarEdgeMap M ≫
          AnodyneKanReplacement.unit.app (monoidBar M)) := by
  rw [loopPathRestriction_ι]
  apply uncurry_injective
  rw [← Category.assoc, uncurry_pre_app, uncurry_curry]
  exact monoidGroupCompletionMap_evaluation M

/--
概要：標準群完備化写像はモノイドの単位をループ空間の基点へ送る。
方針：loop から区間の指数への単射の後で curry を比較し、単位の辺の定数性を使う。
規約：Segal 1974 Proposition 1.5 の点付き標準写像。
使われ方：KST Lemma 2.13 のホモトピー群の基点の整合。
-/
theorem monoidGroupCompletionMap_unit (M : SimplicialObject MonCat.{u}) :
    monoidUnitMap M ≫ monoidGroupCompletionMap M = (monoidGroupCompletionSpace M).hom := by
  let Y := monoidBarKanPointed M
  have : Mono (SSet.const (X := ⊤_ SSet.{u}) Y.basepoint) := by
    exact NatTrans.mono_of_mono_app _
  have : Mono (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι (Spectra.pathEndpoint Y).right Y.basepoint) := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.fiberι
    infer_instance
  have : Mono (loopPathRestriction Y) := by
    rw [← loopPathFiberIso_hom_restriction]
    infer_instance
  apply (cancel_mono (loopPathRestriction Y)).mp
  apply (cancel_mono (PointedObject.basedHomι _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.pointedInterval Y)).mp
  rw [Category.assoc, Category.assoc, monoidGroupCompletionMap_restriction_ι,
    ← curry_natural_left]
  have hr : (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).hom ≫ loopPathRestriction Y =
      (Spectra.basedPathSpace Y).hom :=
    Under.w (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed intervalCircleProjection Y)
  change _ = ((_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.loopSpace Y).hom ≫ loopPathRestriction Y) ≫ _
  rw [hr, PointedObject.basedHom_basepoint_ι]
  change curry _ = curry _
  congr 1
  rw [← Category.assoc, ← Category.assoc, braiding_naturality_right]
  change (β_ (Δ[1] : SSet.{u}) (𝟙_ SSet.{u})).hom ≫
    (monoidUnitMap M ▷ (Δ[1] : SSet.{u}) ≫ monoidBarEdgeMap M) ≫
      AnodyneKanReplacement.unit.app (monoidBar M) =
        toUnit ((Δ[1] : SSet.{u}) ⊗ 𝟙_ SSet.{u}) ≫ Y.hom
  rw [monoidBarEdgeMap_unit, SSet.const_comp]
  have hb : Y.basepoint =
      (AnodyneKanReplacement.unit.app (monoidBar M)).app (op ⦋0⦌)
        (monoidBarBasepoint M) := by
    dsimp only [Y, monoidBarKanPointed]
    rw [PointedSimplicialSet.basepoint_ofVertex]
  have hc : SSet.const (X := (𝟙_ SSet.{u}) ⊗ (Δ[1] : SSet.{u}))
      ((AnodyneKanReplacement.unit.app (monoidBar M)).app (op ⦋0⦌)
        (monoidBarBasepoint M)) = toUnit _ ≫ Y.hom := by
    calc
      _ = SSet.const Y.basepoint := congrArg (fun v => SSet.const v) hb.symm
      _ = _ := const_basepoint _ Y
  exact (congrArg (fun f => (β_ (Δ[1] : SSet.{u}) (𝟙_ SSet.{u})).hom ≫ f) hc).trans
    (by simp only [comp_toUnit_assoc])

end SerrePositivity.KST.Comparison
