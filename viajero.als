//En comentarios, al inicio poner en unos cuantos renglones lo que hace su proyecto

//modulo para utilizar operaciones aritmeticas
module util/integer

pred pos  [n: Int] { n > 0 }


/*
	El problema a resolver es determinar un trayecto entre ciudades 
	el cual el viajero pueda recorrer sin pasar dos veces por la misma 
	ciudad y cuyo costo sea menor o igual al definido por el usuario.
	
	Se deben determinar los costos de viaje entre cada ciudad y 
	eventualmente también se debe poder definir el costo de viaje 
	entre todas las ciudades. El viajero debe poder llegar a todas 
	las ciudades y el trayecto propuesto no debe exceder el costo 
	determinado por el usuario. 

    El problema como tal dice:
        Se tiene un conjunto de ciudades que visitar por un viajero,
        que parte de una de esas ciudades.
        El problema es encontrar una secuencia de ciudades comunicadas,
        tales que el costo es a lo más un costo dado.
*/

//- Código del estado del sistema para su proyecto, con comentarios explicando para qué sirve cada componente
sig Viajero {
	origin: one Ciudad,
	destination: one Ciudad
}

sig Ciudad {}

sig Camino {
	a: one Ciudad,
	b: one Ciudad, // los caminos son reciprocos 
	price : Int //es el precio de una ciudad a otra 
}{
	price >= 0
	from != to
}

sig PopulationState {
	visiting: Viajero one -> one Ciudad,
//	moving: Viajero one -> one Camino,  // sale sobrando
	costoViaje: Viajero -> Int
	visited: Viajero -> set Ciudad
/* Recomendación... un solo viajero */
}


//- Declaración para incluir la utilería de ordenamiento de Alloy
//- Fact con el estado inicial
//- Predicado con la operación para pasar de un estado al siguiente
pred Migrate(ps,ps': PopulationState, traveler: one Viajero, road: one 
Camino) { 
 // precondiciones
// TODO   !!   traveler.current = traveler.(ps.visiting)

//groom+bride in fs.single 
// postcondiciones (cambios)
//groom.(fs'.wife) = bride 
// marco
//fs'.married = fs.married+bride+groom 
} 
//- Fact para el estado siguiente de un estado dado
//- Predicado con la meta para que el sistema entregue una solución
/*

run Migrate for 2

*/

//esto ejecuta el programa 
pred viajero() {} 

run viajero for 4
