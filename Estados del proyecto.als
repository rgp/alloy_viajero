//En comentarios, al inicio poner en unos cuantos renglones lo que hace su proyecto
/*
	El problema a resolver es determinar un trayecto entre ciudades 
	el cual el viajero pueda recorrer sin pasar dos veces por la misma 
	ciudad y cuyo costo sea menor o igual al definido por el usuario.
	
	Se deben determinar los costos de viaje entre cada ciudad y 
	eventualmente también se debe poder definir el costo de viaje 
	entre todas las ciudades. El viajero debe poder llegar a todas 
	las ciudades y el trayecto propuesto no debe exceder el costo 
	determinado por el usuario. 
*/
//- Código del estado del sistema para su proyecto, con comentarios explicando para qué sirve cada componente
sig Viajero {
	origin: lone Ciudad,
	destination: lone Ciudad,
	current: lone Ciudad
}

sig Ciudad {
	adjacent_cities: some Ciudad,
	visitors: set Viajero
}

//- Declaración para incluir la utilería de ordenamiento de Alloy
//- Fact con el estado inicial
//- Predicado con la operación para pasar de un estado al siguiente
//- Fact para el estado siguiente de un estado dado
//- Predicado con la meta para que el sistema entregue una solución
