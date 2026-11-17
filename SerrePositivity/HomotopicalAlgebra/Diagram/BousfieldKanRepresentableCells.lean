module
public import SerrePositivity.HomotopicalAlgebra.Diagram.BousfieldKanFreeCells

/-!
概要：BKの非退化自由細胞の図式は、終頂点の共変表現可能図式の余積。
方針：同じ射列と最後の射の対で余積の包含・降下射を記述し、全射で自然性を検証。
規約：IS-W2 R03aの自由境界細胞の証明分割。型値図式の同じ普遍性。
使われ方：BK骨格の付着を自由評価随伴の境界生成族に同定する。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DiagramModel.BousfieldKanCells
open CategoryTheory Limits Opposite SSet
open scoped Simplicial
variable (I : Type u) [SmallCategory I]

/-- 各非退化射列の終頂点による元の共変表現可能図式。 -/
abbrev cellRepresentables (n : ℕ) (c : (nerve I).nonDegenerate n) : I ⥤ Type u :=
  coyoneda.obj (op (c.val.obj (Fin.last n)))

/-- 各表現可能図式の包含は同じ射列を添える写像。 -/
def freeCellCofan (n : ℕ) : Cofan (cellRepresentables I n) :=
  Cofan.mk (freeCellDiagram I n) (fun c =>
    { app i := ↾fun f => ⟨c, f⟩
      naturality i j f := by
        apply ConcreteCategory.hom_ext
        intro g
        rfl })

/-- 同じ全細胞の射からの降下射。 -/
def freeCellDesc {n : ℕ} {Z : I ⥤ Type u}
    (f : ∀ c, cellRepresentables I n c ⟶ Z) : freeCellDiagram I n ⟶ Z where
  app i := ↾fun s => (f s.1).app i s.2
  naturality i j g := by
    apply ConcreteCategory.hom_ext
    rintro ⟨c, h⟩
    change (f c).app j (h ≫ g) = Z.map g ((f c).app i h)
    exact ConcreteCategory.congr_hom ((f c).naturality g) h

/-- 終頂点の表現可能図式の余積は、同じ非退化自由細胞の図式。 -/
def freeCellCofanIsColimit (n : ℕ) : IsColimit (freeCellCofan I n) := by
  refine Cofan.IsColimit.mk _ (fun s => freeCellDesc I (fun c => s.inj c)) ?_ ?_
  · intro s c
    apply NatTrans.ext
    funext i
    apply ConcreteCategory.hom_ext
    intro f
    rfl
  · intro s m hm
    apply NatTrans.ext
    funext i
    apply ConcreteCategory.hom_ext
    rintro ⟨c, f⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app (hm c) i) f

end SerrePositivity.DiagramModel.BousfieldKanCells
