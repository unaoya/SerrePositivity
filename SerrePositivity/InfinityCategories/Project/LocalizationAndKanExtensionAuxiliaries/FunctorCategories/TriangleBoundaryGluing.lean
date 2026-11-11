module

public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.TriangleBoundaryDecomposition

/-!
概要：合成する二辺と対角辺を、二端点での一致条件だけで境界図式に貼り合わせる。
方針：境界の pushout と、重なり上の射の二端点による外延性を使う。
規約：全ての制限は厳密な等式として保持する。
使われ方：導来 fiber の path を三角形の境界の path へ組み込む。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories

/-- 概要：対角辺の標準区間による表示。
方針：頂点 0 と 2 の面の標準同型。
規約：向きは 0 から 2。
使われ方：指定された path を対角面上へ移す。 -/
noncomputable def triangleDiagonalFaceIso : (Δ[1] : SSet.{u}) ≅
    (stdSimplex.face (n := 2) {0, 2} : SSet.{u}) :=
  stdSimplex.facePairIso (0 : Fin 3) 2 (by decide)

/-- 概要：重なりの始点をホーンへ送ると最初の辺の始点。
方針：ホーンの包含を消去して標準零単体で計算する。
規約：二辺は 0→1 と 1→2。
使われ方：貼り合わせの始点条件。 -/
lemma triangleDiagonalEndpointZero_horn :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointZero.{u} ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₁₂ =
      stdSimplex.δ (1 : Fin 2) ≫ horn₂₁.ι₀₁ := by
  apply (cancel_mono (horn 2 1).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι, horn.ι_ι]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointZero, Category.assoc, Subcomplex.homOfLE_ι]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：重なりの終点をホーンへ送ると最後の辺の終点。
方針：ホーンの包含を消去して標準零単体で計算する。
規約：終点は頂点 2。
使われ方：貼り合わせの終点条件。 -/
lemma triangleDiagonalEndpointTwo_horn :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointTwo.{u} ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₁₂ =
      stdSimplex.δ (0 : Fin 2) ≫ horn₂₁.ι₁₂ := by
  apply (cancel_mono (horn 2 1).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι, horn.ι_ι]
  simp only [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointTwo, Category.assoc, Subcomplex.homOfLE_ι]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：重なりの始点を対角辺の区間へ戻すと時刻零。
方針：面の同型と包含を消去して零単体を計算する。
規約：対角辺の向きは 0→2。
使われ方：指定区間の path の始点を読む。 -/
lemma triangleDiagonalEndpointZero_diagonal :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointZero.{u} ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₁₃ ≫
      triangleDiagonalFaceIso.inv = stdSimplex.δ (1 : Fin 2) := by
  apply (cancel_mono triangleDiagonalFaceIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (stdSimplex.face {0, 2} : (Δ[2] : SSet.{u}).Subcomplex).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointZero]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：重なりの終点を対角辺の区間へ戻すと時刻一。
方針：面の同型と包含を消去して零単体を計算する。
規約：対角辺の向きは 0→2。
使われ方：指定区間の path の終点を読む。 -/
lemma triangleDiagonalEndpointTwo_diagonal :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointTwo.{u} ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₁₃ ≫
      triangleDiagonalFaceIso.inv = stdSimplex.δ (0 : Fin 2) := by
  apply (cancel_mono triangleDiagonalFaceIso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply (cancel_mono (stdSimplex.face {0, 2} : (Δ[2] : SSet.{u}).Subcomplex).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι,
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpointTwo]
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：二辺のホーンと対角辺の図式は二端点の一致から重なり上で一致する。
方針：二端点での外延性と、ホーン・対角辺への端点の公式を使う。
規約：標的 Z は任意の単体集合。
使われ方：境界への descent の厳密な一致条件。 -/
lemma triangleBoundary_gluing_compatible {Z : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ Z)
    (b : (Δ[1] : SSet.{u}) ⟶ Z)
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ b = stdSimplex.δ (1 : Fin 2) ≫ horn₂₁.ι₀₁ ≫ a)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ b = stdSimplex.δ (0 : Fin 2) ≫ horn₂₁.ι₁₂ ≫ a) :
    Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₁₂ ≫ a =
      Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₁₃ ≫ triangleDiagonalFaceIso.inv ≫ b := by
  apply _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleDiagonalEndpoints_hom_ext
  · simpa only [Category.assoc, reassoc_of% triangleDiagonalEndpointZero_horn,
      reassoc_of% triangleDiagonalEndpointZero_diagonal] using h₀.symm
  · simpa only [Category.assoc, reassoc_of% triangleDiagonalEndpointTwo_horn,
      reassoc_of% triangleDiagonalEndpointTwo_diagonal] using h₂.symm

/-- 概要：二辺のホーンと対角辺の図式を三角形の境界へ貼り合わせる。
方針：二端点の一致から pushout の descent を使う。
規約：二辺・対角辺の入力を厳密に回収する。
使われ方：境界上の可逆 path の構成。 -/
noncomputable def triangleBoundaryDiagram {Z : SSet.{u}}
    (a : (horn 2 1 : SSet.{u}) ⟶ Z) (b : (Δ[1] : SSet.{u}) ⟶ Z)
    (h₀ : stdSimplex.δ (1 : Fin 2) ≫ b = stdSimplex.δ (1 : Fin 2) ≫ horn₂₁.ι₀₁ ≫ a)
    (h₂ : stdSimplex.δ (0 : Fin 2) ≫ b = stdSimplex.δ (0 : Fin 2) ≫ horn₂₁.ι₁₂ ≫ a) :
    (boundary 2 : SSet.{u}) ⟶ Z :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.desc a (triangleDiagonalFaceIso.inv ≫ b)
    (triangleBoundary_gluing_compatible a b h₀ h₂)

/-- 概要：貼り合わせた境界図式のホーンへの制限は元の二辺の図式。
方針：pushout の第一包含との合成公式。
規約：厳密な等式。
使われ方：合成する二辺を固定する。 -/
lemma triangleBoundaryDiagram_horn {Z : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ Z)
    (b : (Δ[1] : SSet.{u}) ⟶ Z) (h₀) (h₂) :
    Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ ≫
      triangleBoundaryDiagram a b h₀ h₂ = a :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.inl_desc _ _ _

/-- 概要：貼り合わせた境界図式の対角面への制限は元の区間図式。
方針：pushout の第二包含との合成公式。
規約：面から標準区間へ戻す同型を付ける。
使われ方：対角辺の path を保持する。 -/
lemma triangleBoundaryDiagram_diagonal_face {Z : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ Z)
    (b : (Δ[1] : SSet.{u}) ⟶ Z) (h₀) (h₂) :
    Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₃₄ ≫
      triangleBoundaryDiagram a b h₀ h₂ = triangleDiagonalFaceIso.inv ≫ b :=
  _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_isPushout.inr_desc _ _ _

/-- 概要：対角面の標準表示を周囲へ含めると δ₁。
方針：Yoneda で標準一次単体の有限順序写像を計算する。
規約：対角面は頂点 0 と 2。
使われ方：貼り合わせた図式を標準面で検査する。 -/
lemma triangleDiagonalFaceIso_hom_ι :
    triangleDiagonalFaceIso.{u}.hom ≫ (stdSimplex.face {0, 2}).ι =
      stdSimplex.δ (1 : Fin 3) := by
  apply SSet.yonedaEquiv.injective
  decide

/-- 概要：対角面の標準表示を境界へ含めると境界の第 1 面。
方針：周囲の単体への包含を消去する。
規約：三角形の境界内での厳密な等式。
使われ方：対角辺の制限を取り出す。 -/
lemma triangleDiagonalFaceIso_hom_boundary :
    triangleDiagonalFaceIso.{u}.hom ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₃₄ =
      boundary.ι (1 : Fin 3) := by
  apply (cancel_mono (boundary 2).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι, boundary.ι_ι]
  exact triangleDiagonalFaceIso_hom_ι

/-- 概要：合成ホーンの前辺を境界へ含めると第 2 面。
方針：周囲の単体への包含を消去する。
規約：前辺は 0→1。
使われ方：固定した前辺の制限を取り出す。 -/
lemma triangleBoundary_horn_front :
    horn₂₁.ι₀₁.{u} ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ =
      boundary.ι (2 : Fin 3) := by
  apply (cancel_mono (boundary 2).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι, horn.ι_ι, boundary.ι_ι]

/-- 概要：合成ホーンの後辺を境界へ含めると第 0 面。
方針：周囲の単体への包含を消去する。
規約：後辺は 1→2。
使われ方：固定した後辺の制限を取り出す。 -/
lemma triangleBoundary_horn_back :
    horn₂₁.ι₁₂.{u} ≫ Subcomplex.homOfLE _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleBoundary_bicartSq.le₂₄ =
      boundary.ι (0 : Fin 3) := by
  apply (cancel_mono (boundary 2).ι).mp
  simp only [Category.assoc, Subcomplex.homOfLE_ι, horn.ι_ι, boundary.ι_ι]

/-- 概要：貼り合わせた境界図式の第 1 面は指定対角辺。
方針：対角面の表示同型と pushout の第二制限公式を使う。
規約：厳密な等式。
使われ方：導来 fiber の path を回収する。 -/
lemma triangleBoundaryDiagram_face_one {Z : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ Z)
    (b : (Δ[1] : SSet.{u}) ⟶ Z) (h₀) (h₂) :
    boundary.ι (1 : Fin 3) ≫ triangleBoundaryDiagram a b h₀ h₂ = b := by
  rw [← triangleDiagonalFaceIso_hom_boundary, Category.assoc,
    triangleBoundaryDiagram_diagonal_face, Iso.hom_inv_id_assoc]

/-- 概要：貼り合わせた境界図式の第 2 面は指定ホーンの前辺。
方針：ホーンの包含と pushout の第一制限公式を使う。
規約：厳密な等式。
使われ方：合成する前辺を保持する。 -/
lemma triangleBoundaryDiagram_face_two {Z : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ Z)
    (b : (Δ[1] : SSet.{u}) ⟶ Z) (h₀) (h₂) :
    boundary.ι (2 : Fin 3) ≫ triangleBoundaryDiagram a b h₀ h₂ = horn₂₁.ι₀₁ ≫ a := by
  rw [← triangleBoundary_horn_front, Category.assoc, triangleBoundaryDiagram_horn]

/-- 概要：貼り合わせた境界図式の第 0 面は指定ホーンの後辺。
方針：ホーンの包含と pushout の第一制限公式を使う。
規約：厳密な等式。
使われ方：合成する後辺を保持する。 -/
lemma triangleBoundaryDiagram_face_zero {Z : SSet.{u}} (a : (horn 2 1 : SSet.{u}) ⟶ Z)
    (b : (Δ[1] : SSet.{u}) ⟶ Z) (h₀) (h₂) :
    boundary.ι (0 : Fin 3) ≫ triangleBoundaryDiagram a b h₀ h₂ = horn₂₁.ι₁₂ ≫ a := by
  rw [← triangleBoundary_horn_back, Category.assoc, triangleBoundaryDiagram_horn]

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
