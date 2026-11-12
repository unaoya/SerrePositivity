module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping
public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanHomotopyExtension

/-!
概要：anodyne な点つき射に沿う Kan 標的への点つき延長。
方針：基礎単体集合で延長し、元の基点が像に含まれることから基点保存を得る。
規約：源と中間対象の Kan 性は不要。
使われ方：Goerss–Jardine I §7、HTT A.3.3。列の Kan 置換の構造射。
-/

@[expose] public section

universe u

open CategoryTheory Limits SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen

namespace SerrePositivity.KST.Spectra.PointedExtension

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：anodyne な点つき射に沿って Kan 標的への点つき射を延長できる。
方針：基礎の延長の可換式で標的の基点を検査する。
規約：延長の選択に自然性は主張しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。Kan 置換の構造写像。 -/
theorem exists_extension {A B Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i.right) (f : A ⟶ Z) :
    ∃ g : B ⟶ Z, i ≫ g = f := by
  have hZ : J.rlp (terminal.from Z.right) := (fibration_iff _).1 inferInstance
  obtain ⟨g, hg⟩ :=
    SerrePositivity.SimplicialModel.KanHomotopyExtension.exists_extension i.right hi hZ f.right
  have hb : B.hom ≫ g = Z.hom := by
    rw [← Under.w i, Category.assoc, hg, Under.w]
  refine ⟨Under.homMk g hb, ?_⟩
  apply Under.UnderMorphism.ext
  exact hg

/-- 概要：一つの実際の点つき延長を選ぶ。
方針：anodyne 射の延長の存在から選択する。
規約：選択の自然性は要求しない。
使われ方：Goerss–Jardine I §7、HTT A.3.3。列の置換の構造射のデータ。 -/
def extend {A B Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i.right) (f : A ⟶ Z) : B ⟶ Z :=
  (exists_extension i hi f).choose

/-- 概要：選んだ延長を元の対象へ制限すると元の射になる。
方針：存在の証明の可換条件を使う。
規約：点つき射の厳密な等式。
使われ方：Goerss–Jardine I §7、HTT A.3.3。置換の比較射の厳密可換性。 -/
@[reassoc (attr := simp)]
theorem comp_extend {A B Z : PointedSimplicialSet.{u}} [KanComplex Z.right]
    (i : A ⟶ B) (hi : SSet.anodyneExtensions i.right) (f : A ⟶ Z) : i ≫ extend i hi f = f :=
  (exists_extension i hi f).choose_spec

end

end SerrePositivity.KST.Spectra.PointedExtension
